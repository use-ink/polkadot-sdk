// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! The paras pallet acts as the main registry of paras.
//!
//! # Tracking State of Paras
//!
//! The most important responsibility of this module is to track which parachains
//! are active and what their current state is. The current state of a para consists of the current
//! head data and the current validation code (AKA Parachain Validation Function (PVF)).
//!
//! A para is not considered live until it is registered and activated in this pallet.
//!
//! The set of parachains cannot change except at session boundaries. This is primarily to ensure
//! that the number and meaning of bits required for the availability bitfields does not change
//! except at session boundaries.
//!
//! # Validation Code Upgrades
//!
//! When a para signals the validation code upgrade it will be processed by this module. This can
//! be in turn split into more fine grained items:
//!
//! - Part of the acceptance criteria checks if the para can indeed signal an upgrade,
//!
//! - When the candidate is enacted, this module schedules code upgrade, storing the prospective
//!   validation code.
//!
//! - Actually assign the prospective validation code to be the current one after all conditions are
//!   fulfilled.
//!
//! The conditions that must be met before the para can use the new validation code are:
//!
//! 1. The validation code should have been "soaked" in the storage for a given number of blocks.
//! That    is, the validation code should have been stored in on-chain storage for some time, so
//! that in    case of a revert with a non-extreme height difference, that validation code can still
//! be    found on-chain.
//!
//! 2. The validation code was vetted by the validators and declared as non-malicious in a processes
//!    known as PVF pre-checking.
//!
//! # Validation Code Management
//!
//! Potentially, one validation code can be used by several different paras. For example, during
//! initial stages of deployment several paras can use the same "shell" validation code, or
//! there can be shards of the same para that use the same validation code.
//!
//! In case a validation code ceases to have any users it must be pruned from the on-chain storage.
//!
//! # Para Lifecycle Management
//!
//! A para can be in one of the two stable states: it is either a lease holding parachain or an
//! on-demand parachain.
//!
//! However, in order to get into one of those two states, it must first be onboarded. Onboarding
//! can be only enacted at session boundaries. Onboarding must take at least one full session.
//! Moreover, a brand new validation code should go through the PVF pre-checking process.
//!
//! Once the para is in one of the two stable states, it can switch to the other stable state or to
//! initiate offboarding process. The result of offboarding is removal of all data related to that
//! para.
//!
//! # PVF Pre-checking
//!
//! As was mentioned above, a brand new validation code should go through a process of approval. As
//! part of this process, validators from the active set will take the validation code and check if
//! it is malicious. Once they did that and have their judgement, either accept or reject, they
//! issue a statement in a form of an unsigned extrinsic. This extrinsic is processed by this
//! pallet. Once supermajority is gained for accept, then the process that initiated the check is
//! resumed (as mentioned before this can be either upgrading of validation code or onboarding). If
//! getting a supermajority becomes impossible (>1/3 of validators have already voted against), then
//! we reject.
//!
//! Below is a state diagram that depicts states of a single PVF pre-checking vote.
//!
//! ```text
//!                                            ┌──────────┐
//!                        supermajority       │          │
//!                    ┌────────for───────────▶│ accepted │
//!        vote────┐   │                       │          │
//!         │      │   │                       └──────────┘
//!         │      │   │
//!         │  ┌───────┐
//!         │  │       │
//!         └─▶│ init  │──── >1/3 against      ┌──────────┐
//!            │       │           │           │          │
//!            └───────┘           └──────────▶│ rejected │
//!             ▲  │                           │          │
//!             │  │ session                   └──────────┘
//!             │  └──change
//!             │     │
//!             │     ▼
//!             ┌─────┐
//! start──────▶│reset│
//!             └─────┘
//! ```

use crate::{
	configuration,
	inclusion::{QueueFootprinter, UmpQueueId},
	initializer::SessionChangeNotification,
	shared,
};
use alloc::{collections::btree_set::BTreeSet, vec::Vec};
use bitvec::{order::Lsb0 as BitOrderLsb0, vec::BitVec};
use codec::{Decode, Encode};
use core::{cmp, mem};
use frame_support::{
	pallet_prelude::*,
	traits::{EnsureOriginWithArg, EstimateNextSessionRotation},
	DefaultNoBound,
};
use frame_system::pallet_prelude::*;
use polkadot_primitives::{
	ConsensusLog, HeadData, Id as ParaId, PvfCheckStatement, SessionIndex, UpgradeGoAhead,
	UpgradeRestriction, ValidationCode, ValidationCodeHash, ValidatorSignature, MIN_CODE_SIZE,
};
use scale_info::{Type, TypeInfo};
use sp_core::RuntimeDebug;
use sp_runtime::{
	traits::{AppVerify, One, Saturating},
	DispatchResult, SaturatedConversion,
};

use serde::{Deserialize, Serialize};

pub use crate::Origin as ParachainOrigin;

#[cfg(feature = "runtime-benchmarks")]
pub mod benchmarking;

#[cfg(test)]
pub(crate) mod tests;

pub use pallet::*;

const LOG_TARGET: &str = "runtime::paras";

// the two key times necessary to track for every code replacement.
#[derive(Default, Encode, Decode, TypeInfo)]
#[cfg_attr(test, derive(Debug, Clone, PartialEq))]
pub struct ReplacementTimes<N> {
	/// The relay-chain block number that the code upgrade was expected to be activated.
	/// This is when the code change occurs from the para's perspective - after the
	/// first parablock included with a relay-parent with number >= this value.
	expected_at: N,
	/// The relay-chain block number at which the parablock activating the code upgrade was
	/// actually included. This means considered included and available, so this is the time at
	/// which that parablock enters the acceptance period in this fork of the relay-chain.
	activated_at: N,
}

/// Metadata used to track previous parachain validation code that we keep in
/// the state.
#[derive(Default, Encode, Decode, TypeInfo)]
#[cfg_attr(test, derive(Debug, Clone, PartialEq))]
pub struct ParaPastCodeMeta<N> {
	/// Block numbers where the code was expected to be replaced and where the code
	/// was actually replaced, respectively. The first is used to do accurate look-ups
	/// of historic code in historic contexts, whereas the second is used to do
	/// pruning on an accurate timeframe. These can be used as indices
	/// into the `PastCodeHash` map along with the `ParaId` to fetch the code itself.
	upgrade_times: Vec<ReplacementTimes<N>>,
	/// Tracks the highest pruned code-replacement, if any. This is the `activated_at` value,
	/// not the `expected_at` value.
	last_pruned: Option<N>,
}

/// The possible states of a para, to take into account delayed lifecycle changes.
///
/// If the para is in a "transition state", it is expected that the parachain is
/// queued in the `ActionsQueue` to transition it into a stable state. Its lifecycle
/// state will be used to determine the state transition to apply to the para.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum ParaLifecycle {
	/// Para is new and is onboarding as an on-demand or lease holding Parachain.
	Onboarding,
	/// Para is a Parathread (on-demand parachain).
	Parathread,
	/// Para is a lease holding Parachain.
	Parachain,
	/// Para is a Parathread (on-demand parachain) which is upgrading to a lease holding Parachain.
	UpgradingParathread,
	/// Para is a lease holding Parachain which is downgrading to an on-demand parachain.
	DowngradingParachain,
	/// Parathread (on-demand parachain) is queued to be offboarded.
	OffboardingParathread,
	/// Parachain is queued to be offboarded.
	OffboardingParachain,
}

impl ParaLifecycle {
	/// Returns true if parachain is currently onboarding. To learn if the
	/// parachain is onboarding as a lease holding or on-demand parachain, look at the
	/// `UpcomingGenesis` storage item.
	pub fn is_onboarding(&self) -> bool {
		matches!(self, ParaLifecycle::Onboarding)
	}

	/// Returns true if para is in a stable state, i.e. it is currently
	/// a lease holding or on-demand parachain, and not in any transition state.
	pub fn is_stable(&self) -> bool {
		matches!(self, ParaLifecycle::Parathread | ParaLifecycle::Parachain)
	}

	/// Returns true if para is currently treated as a parachain.
	/// This also includes transitioning states, so you may want to combine
	/// this check with `is_stable` if you specifically want `Paralifecycle::Parachain`.
	pub fn is_parachain(&self) -> bool {
		matches!(
			self,
			ParaLifecycle::Parachain |
				ParaLifecycle::DowngradingParachain |
				ParaLifecycle::OffboardingParachain
		)
	}

	/// Returns true if para is currently treated as a parathread (on-demand parachain).
	/// This also includes transitioning states, so you may want to combine
	/// this check with `is_stable` if you specifically want `Paralifecycle::Parathread`.
	pub fn is_parathread(&self) -> bool {
		matches!(
			self,
			ParaLifecycle::Parathread |
				ParaLifecycle::UpgradingParathread |
				ParaLifecycle::OffboardingParathread
		)
	}

	/// Returns true if para is currently offboarding.
	pub fn is_offboarding(&self) -> bool {
		matches!(self, ParaLifecycle::OffboardingParathread | ParaLifecycle::OffboardingParachain)
	}

	/// Returns true if para is in any transitionary state.
	pub fn is_transitioning(&self) -> bool {
		!Self::is_stable(self)
	}
}

impl<N: Ord + Copy + PartialEq> ParaPastCodeMeta<N> {
	// note a replacement has occurred at a given block number.
	pub(crate) fn note_replacement(&mut self, expected_at: N, activated_at: N) {
		self.upgrade_times.push(ReplacementTimes { expected_at, activated_at })
	}

	/// Returns `true` if the upgrade logs list is empty.
	fn is_empty(&self) -> bool {
		self.upgrade_times.is_empty()
	}

	// The block at which the most recently tracked code change occurred, from the perspective
	// of the para.
	#[cfg(test)]
	fn most_recent_change(&self) -> Option<N> {
		self.upgrade_times.last().map(|x| x.expected_at)
	}

	// prunes all code upgrade logs occurring at or before `max`.
	// note that code replaced at `x` is the code used to validate all blocks before
	// `x`. Thus, `max` should be outside of the slashing window when this is invoked.
	//
	// Since we don't want to prune anything inside the acceptance period, and the parablock only
	// enters the acceptance period after being included, we prune based on the activation height of
	// the code change, not the expected height of the code change.
	//
	// returns an iterator of block numbers at which code was replaced, where the replaced
	// code should be now pruned, in ascending order.
	fn prune_up_to(&'_ mut self, max: N) -> impl Iterator<Item = N> + '_ {
		let to_prune = self.upgrade_times.iter().take_while(|t| t.activated_at <= max).count();
		let drained = if to_prune == 0 {
			// no-op prune.
			self.upgrade_times.drain(self.upgrade_times.len()..)
		} else {
			// if we are actually pruning something, update the `last_pruned` member.
			self.last_pruned = Some(self.upgrade_times[to_prune - 1].activated_at);
			self.upgrade_times.drain(..to_prune)
		};

		drained.map(|times| times.expected_at)
	}
}

/// Arguments for initializing a para.
#[derive(
	PartialEq,
	Eq,
	Clone,
	Encode,
	Decode,
	DecodeWithMemTracking,
	RuntimeDebug,
	TypeInfo,
	Serialize,
	Deserialize,
)]
pub struct ParaGenesisArgs {
	/// The initial head data to use.
	pub genesis_head: HeadData,
	/// The initial validation code to use.
	pub validation_code: ValidationCode,
	/// Lease holding or on-demand parachain.
	#[serde(rename = "parachain")]
	pub para_kind: ParaKind,
}

/// Distinguishes between lease holding Parachain and Parathread (on-demand parachain)
#[derive(DecodeWithMemTracking, PartialEq, Eq, Clone, RuntimeDebug)]
pub enum ParaKind {
	Parathread,
	Parachain,
}

impl Serialize for ParaKind {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: serde::Serializer,
	{
		match self {
			ParaKind::Parachain => serializer.serialize_bool(true),
			ParaKind::Parathread => serializer.serialize_bool(false),
		}
	}
}

impl<'de> Deserialize<'de> for ParaKind {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: serde::Deserializer<'de>,
	{
		match serde::de::Deserialize::deserialize(deserializer) {
			Ok(true) => Ok(ParaKind::Parachain),
			Ok(false) => Ok(ParaKind::Parathread),
			_ => Err(serde::de::Error::custom("invalid ParaKind serde representation")),
		}
	}
}

// Manual encoding, decoding, and TypeInfo as the parakind field in ParaGenesisArgs used to be a
// bool
impl Encode for ParaKind {
	fn size_hint(&self) -> usize {
		true.size_hint()
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		match self {
			ParaKind::Parachain => true.using_encoded(f),
			ParaKind::Parathread => false.using_encoded(f),
		}
	}
}

impl Decode for ParaKind {
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		match bool::decode(input) {
			Ok(true) => Ok(ParaKind::Parachain),
			Ok(false) => Ok(ParaKind::Parathread),
			_ => Err("Invalid ParaKind representation".into()),
		}
	}
}

impl TypeInfo for ParaKind {
	type Identity = bool;
	fn type_info() -> Type {
		bool::type_info()
	}
}

/// This enum describes a reason why a particular PVF pre-checking vote was initiated. When the
/// PVF vote in question is concluded, this enum indicates what changes should be performed.
#[derive(Debug, Encode, Decode, TypeInfo)]
pub(crate) enum PvfCheckCause<BlockNumber> {
	/// PVF vote was initiated by the initial onboarding process of the given para.
	Onboarding(ParaId),
	/// PVF vote was initiated by signalling of an upgrade by the given para.
	Upgrade {
		/// The ID of the parachain that initiated or is waiting for the conclusion of
		/// pre-checking.
		id: ParaId,
		/// The relay-chain block number of **inclusion** of candidate that that initiated the
		/// upgrade.
		///
		/// It's important to count upgrade enactment delay from the inclusion of this candidate
		/// instead of its relay parent -- in order to keep PVF available in case of chain
		/// reversions.
		///
		/// See https://github.com/paritytech/polkadot/issues/4601 for detailed explanation.
		included_at: BlockNumber,
		/// Whether or not the upgrade should be enacted directly.
		///
		/// If set to `Yes` it means that no `GoAheadSignal` will be set and the parachain code
		/// will also be overwritten directly.
		upgrade_strategy: UpgradeStrategy,
	},
}

/// The strategy on how to handle a validation code upgrade.
///
/// When scheduling a parachain code upgrade the upgrade first is checked by all validators. The
/// validators ensure that the new validation code can be compiled and instantiated. After the
/// majority of the validators have reported their checking result the upgrade is either scheduled
/// or aborted. This strategy then comes into play around the relay chain block this upgrade was
/// scheduled in.
#[derive(Debug, Copy, Clone, PartialEq, TypeInfo, Decode, Encode)]
pub enum UpgradeStrategy {
	/// Set the `GoAhead` signal to inform the parachain that it is time to upgrade.
	///
	/// The upgrade will then be applied after the first parachain block was enacted that must have
	/// observed the `GoAhead` signal.
	SetGoAheadSignal,
	/// Apply the upgrade directly at the expected relay chain block.
	///
	/// This doesn't wait for the parachain to make any kind of progress.
	ApplyAtExpectedBlock,
}

impl<BlockNumber> PvfCheckCause<BlockNumber> {
	/// Returns the ID of the para that initiated or subscribed to the pre-checking vote.
	fn para_id(&self) -> ParaId {
		match *self {
			PvfCheckCause::Onboarding(id) => id,
			PvfCheckCause::Upgrade { id, .. } => id,
		}
	}
}

/// Specifies what was the outcome of a PVF pre-checking vote.
#[derive(Copy, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
enum PvfCheckOutcome {
	Accepted,
	Rejected,
}

/// This struct describes the current state of an in-progress PVF pre-checking vote.
#[derive(Encode, Decode, TypeInfo)]
pub(crate) struct PvfCheckActiveVoteState<BlockNumber> {
	// The two following vectors have their length equal to the number of validators in the active
	// set. They start with all zeroes. A 1 is set at an index when the validator at the that index
	// makes a vote. Once a 1 is set for either of the vectors, that validator cannot vote anymore.
	// Since the active validator set changes each session, the bit vectors are reinitialized as
	// well: zeroed and resized so that each validator gets its own bit.
	votes_accept: BitVec<u8, BitOrderLsb0>,
	votes_reject: BitVec<u8, BitOrderLsb0>,

	/// The number of session changes this PVF vote has observed. Therefore, this number is
	/// increased at each session boundary. When created, it is initialized with 0.
	age: SessionIndex,
	/// The block number at which this PVF vote was created.
	created_at: BlockNumber,
	/// A list of causes for this PVF pre-checking. Has at least one.
	causes: Vec<PvfCheckCause<BlockNumber>>,
}

impl<BlockNumber> PvfCheckActiveVoteState<BlockNumber> {
	/// Returns a new instance of vote state, started at the specified block `now`, with the
	/// number of validators in the current session `n_validators` and the originating `cause`.
	fn new(now: BlockNumber, n_validators: usize, cause: PvfCheckCause<BlockNumber>) -> Self {
		let mut causes = Vec::with_capacity(1);
		causes.push(cause);
		Self {
			created_at: now,
			votes_accept: bitvec::bitvec![u8, BitOrderLsb0; 0; n_validators],
			votes_reject: bitvec::bitvec![u8, BitOrderLsb0; 0; n_validators],
			age: 0,
			causes,
		}
	}

	/// Resets all votes and resizes the votes vectors corresponding to the number of validators
	/// in the new session.
	fn reinitialize_ballots(&mut self, n_validators: usize) {
		let clear_and_resize = |v: &mut BitVec<_, _>| {
			v.clear();
			v.resize(n_validators, false);
		};
		clear_and_resize(&mut self.votes_accept);
		clear_and_resize(&mut self.votes_reject);
	}

	/// Returns `Some(true)` if the validator at the given index has already cast their vote within
	/// the ongoing session. Returns `None` in case the index is out of bounds.
	fn has_vote(&self, validator_index: usize) -> Option<bool> {
		let accept_vote = self.votes_accept.get(validator_index)?;
		let reject_vote = self.votes_reject.get(validator_index)?;
		Some(*accept_vote || *reject_vote)
	}

	/// Returns `None` if the quorum is not reached, or the direction of the decision.
	fn quorum(&self, n_validators: usize) -> Option<PvfCheckOutcome> {
		let accept_threshold = polkadot_primitives::supermajority_threshold(n_validators);
		// At this threshold, a supermajority is no longer possible, so we reject.
		let reject_threshold = n_validators - accept_threshold;

		if self.votes_accept.count_ones() >= accept_threshold {
			Some(PvfCheckOutcome::Accepted)
		} else if self.votes_reject.count_ones() > reject_threshold {
			Some(PvfCheckOutcome::Rejected)
		} else {
			None
		}
	}

	#[cfg(test)]
	pub(crate) fn causes(&self) -> &[PvfCheckCause<BlockNumber>] {
		self.causes.as_slice()
	}
}

/// Runtime hook for when a parachain head is updated.
pub trait OnNewHead {
	/// Called when a parachain head is updated.
	/// Returns the weight consumed by this function.
	fn on_new_head(id: ParaId, head: &HeadData) -> Weight;
}

#[impl_trait_for_tuples::impl_for_tuples(30)]
impl OnNewHead for Tuple {
	fn on_new_head(id: ParaId, head: &HeadData) -> Weight {
		let mut weight: Weight = Default::default();
		for_tuples!( #( weight.saturating_accrue(Tuple::on_new_head(id, head)); )* );
		weight
	}
}

/// Assign coretime to some parachain.
///
/// This assigns coretime to a parachain without using the coretime chain. Thus, this should only be
/// used for testing purposes.
pub trait AssignCoretime {
	/// ONLY USE FOR TESTING OR GENESIS.
	fn assign_coretime(id: ParaId) -> DispatchResult;
}

impl AssignCoretime for () {
	fn assign_coretime(_: ParaId) -> DispatchResult {
		Ok(())
	}
}

/// Holds an authorized validation code hash along with its expiry timestamp.
#[derive(Debug, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(test, derive(PartialEq))]
pub struct AuthorizedCodeHashAndExpiry<T> {
	code_hash: ValidationCodeHash,
	expire_at: T,
}
impl<T> From<(ValidationCodeHash, T)> for AuthorizedCodeHashAndExpiry<T> {
	fn from(value: (ValidationCodeHash, T)) -> Self {
		AuthorizedCodeHashAndExpiry { code_hash: value.0, expire_at: value.1 }
	}
}

pub trait WeightInfo {
	fn force_set_current_code(c: u32) -> Weight;
	fn force_set_current_head(s: u32) -> Weight;
	fn force_set_most_recent_context() -> Weight;
	fn force_schedule_code_upgrade(c: u32) -> Weight;
	fn force_note_new_head(s: u32) -> Weight;
	fn force_queue_action() -> Weight;
	fn add_trusted_validation_code(c: u32) -> Weight;
	fn poke_unused_validation_code() -> Weight;
	fn remove_upgrade_cooldown() -> Weight;

	fn include_pvf_check_statement_finalize_upgrade_accept() -> Weight;
	fn include_pvf_check_statement_finalize_upgrade_reject() -> Weight;
	fn include_pvf_check_statement_finalize_onboarding_accept() -> Weight;
	fn include_pvf_check_statement_finalize_onboarding_reject() -> Weight;
	fn include_pvf_check_statement() -> Weight;
	fn authorize_force_set_current_code_hash() -> Weight;
	fn apply_authorized_force_set_current_code(c: u32) -> Weight;
}

pub struct TestWeightInfo;
impl WeightInfo for TestWeightInfo {
	fn force_set_current_code(_c: u32) -> Weight {
		Weight::MAX
	}
	fn force_set_current_head(_s: u32) -> Weight {
		Weight::MAX
	}
	fn force_set_most_recent_context() -> Weight {
		Weight::MAX
	}
	fn force_schedule_code_upgrade(_c: u32) -> Weight {
		Weight::MAX
	}
	fn force_note_new_head(_s: u32) -> Weight {
		Weight::MAX
	}
	fn force_queue_action() -> Weight {
		Weight::MAX
	}
	fn add_trusted_validation_code(_c: u32) -> Weight {
		// Called during integration tests for para initialization.
		Weight::zero()
	}
	fn poke_unused_validation_code() -> Weight {
		Weight::MAX
	}
	fn include_pvf_check_statement_finalize_upgrade_accept() -> Weight {
		Weight::MAX
	}
	fn include_pvf_check_statement_finalize_upgrade_reject() -> Weight {
		Weight::MAX
	}
	fn include_pvf_check_statement_finalize_onboarding_accept() -> Weight {
		Weight::MAX
	}
	fn include_pvf_check_statement_finalize_onboarding_reject() -> Weight {
		Weight::MAX
	}
	fn include_pvf_check_statement() -> Weight {
		// This special value is to distinguish from the finalizing variants above in tests.
		Weight::MAX - Weight::from_parts(1, 1)
	}
	fn remove_upgrade_cooldown() -> Weight {
		Weight::MAX
	}
	fn authorize_force_set_current_code_hash() -> Weight {
		Weight::MAX
	}
	fn apply_authorized_force_set_current_code(_c: u32) -> Weight {
		Weight::MAX
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::traits::{
		fungible::{Inspect, Mutate},
		tokens::{Fortitude, Precision, Preservation},
	};
	use sp_runtime::transaction_validity::{
		InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
		ValidTransaction,
	};

	type BalanceOf<T> = <<T as Config>::Fungible as Inspect<AccountIdFor<T>>>::Balance;

	#[pallet::pallet]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ configuration::Config
		+ shared::Config
		+ frame_system::offchain::CreateBare<Call<Self>>
	{
		#[allow(deprecated)]
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		#[pallet::constant]
		type UnsignedPriority: Get<TransactionPriority>;

		type NextSessionRotation: EstimateNextSessionRotation<BlockNumberFor<Self>>;

		/// Retrieve how many UMP messages are enqueued for this para-chain.
		///
		/// This is used to judge whether or not a para-chain can offboard. Per default this should
		/// be set to the `ParaInclusion` pallet.
		type QueueFootprinter: QueueFootprinter<Origin = UmpQueueId>;

		/// Runtime hook for when a parachain head is updated.
		type OnNewHead: OnNewHead;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// Runtime hook for assigning coretime for a given parachain.
		///
		/// This is only used at genesis or by root.
		///
		/// TODO: Remove once coretime is the standard across all chains.
		type AssignCoretime: AssignCoretime;

		/// The fungible instance used by the runtime.
		type Fungible: Mutate<Self::AccountId, Balance: From<BlockNumberFor<Self>>>;

		/// Multiplier to determine the cost of removing upgrade cooldown.
		///
		/// After a parachain upgrades their runtime, an upgrade cooldown is applied
		/// ([`configuration::HostConfiguration::validation_upgrade_cooldown`]). This cooldown
		/// exists to prevent spamming the relay chain with runtime upgrades. But as life is going
		/// on, mistakes can happen and a consequent may be required. The cooldown period can be
		/// removed by using [`Pallet::remove_upgrade_cooldown`]. This dispatchable will use this
		/// multiplier to determine the cost for removing the upgrade cooldown. Time left for the
		/// cooldown multiplied with this multiplier determines the cost.
		type CooldownRemovalMultiplier: Get<BalanceOf<Self>>;

		/// The origin that can authorize [`Pallet::authorize_force_set_current_code_hash`].
		///
		/// In the end this allows [`Pallet::apply_authorized_force_set_current_code`] to force set
		/// the current code without paying any fee. So, the origin should be chosen with care.
		type AuthorizeCurrentCodeOrigin: EnsureOriginWithArg<Self::RuntimeOrigin, ParaId>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Current code has been updated for a Para. `para_id`
		CurrentCodeUpdated(ParaId),
		/// Current head has been updated for a Para. `para_id`
		CurrentHeadUpdated(ParaId),
		/// A code upgrade has been scheduled for a Para. `para_id`
		CodeUpgradeScheduled(ParaId),
		/// A new head has been noted for a Para. `para_id`
		NewHeadNoted(ParaId),
		/// A para has been queued to execute pending actions. `para_id`
		ActionQueued(ParaId, SessionIndex),
		/// The given para either initiated or subscribed to a PVF check for the given validation
		/// code. `code_hash` `para_id`
		PvfCheckStarted(ValidationCodeHash, ParaId),
		/// The given validation code was accepted by the PVF pre-checking vote.
		/// `code_hash` `para_id`
		PvfCheckAccepted(ValidationCodeHash, ParaId),
		/// The given validation code was rejected by the PVF pre-checking vote.
		/// `code_hash` `para_id`
		PvfCheckRejected(ValidationCodeHash, ParaId),
		/// The upgrade cooldown was removed.
		UpgradeCooldownRemoved {
			/// The parachain for which the cooldown got removed.
			para_id: ParaId,
		},
		/// A new code hash has been authorized for a Para.
		CodeAuthorized {
			/// Para
			para_id: ParaId,
			/// Authorized code hash.
			code_hash: ValidationCodeHash,
			/// Block at which authorization expires and will be removed.
			expire_at: BlockNumberFor<T>,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Para is not registered in our system.
		NotRegistered,
		/// Para cannot be onboarded because it is already tracked by our system.
		CannotOnboard,
		/// Para cannot be offboarded at this time.
		CannotOffboard,
		/// Para cannot be upgraded to a lease holding parachain.
		CannotUpgrade,
		/// Para cannot be downgraded to an on-demand parachain.
		CannotDowngrade,
		/// The statement for PVF pre-checking is stale.
		PvfCheckStatementStale,
		/// The statement for PVF pre-checking is for a future session.
		PvfCheckStatementFuture,
		/// Claimed validator index is out of bounds.
		PvfCheckValidatorIndexOutOfBounds,
		/// The signature for the PVF pre-checking is invalid.
		PvfCheckInvalidSignature,
		/// The given validator already has cast a vote.
		PvfCheckDoubleVote,
		/// The given PVF does not exist at the moment of process a vote.
		PvfCheckSubjectInvalid,
		/// Parachain cannot currently schedule a code upgrade.
		CannotUpgradeCode,
		/// Invalid validation code size.
		InvalidCode,
		/// No upgrade authorized.
		NothingAuthorized,
		/// The submitted code is not authorized.
		Unauthorized,
		/// Invalid block number.
		InvalidBlockNumber,
	}

	/// All currently active PVF pre-checking votes.
	///
	/// Invariant:
	/// - There are no PVF pre-checking votes that exists in list but not in the set and vice versa.
	#[pallet::storage]
	pub(super) type PvfActiveVoteMap<T: Config> = StorageMap<
		_,
		Twox64Concat,
		ValidationCodeHash,
		PvfCheckActiveVoteState<BlockNumberFor<T>>,
		OptionQuery,
	>;

	/// The list of all currently active PVF votes. Auxiliary to `PvfActiveVoteMap`.
	#[pallet::storage]
	pub(super) type PvfActiveVoteList<T: Config> =
		StorageValue<_, Vec<ValidationCodeHash>, ValueQuery>;

	/// All lease holding parachains. Ordered ascending by `ParaId`. On demand parachains are not
	/// included.
	///
	/// Consider using the [`ParachainsCache`] type of modifying.
	#[pallet::storage]
	pub type Parachains<T: Config> = StorageValue<_, Vec<ParaId>, ValueQuery>;

	/// The current lifecycle of a all known Para IDs.
	#[pallet::storage]
	pub(super) type ParaLifecycles<T: Config> = StorageMap<_, Twox64Concat, ParaId, ParaLifecycle>;

	/// The head-data of every registered para.
	#[pallet::storage]
	pub type Heads<T: Config> = StorageMap<_, Twox64Concat, ParaId, HeadData>;

	/// The context (relay-chain block number) of the most recent parachain head.
	#[pallet::storage]
	pub type MostRecentContext<T: Config> = StorageMap<_, Twox64Concat, ParaId, BlockNumberFor<T>>;

	/// The validation code hash of every live para.
	///
	/// Corresponding code can be retrieved with [`CodeByHash`].
	#[pallet::storage]
	pub type CurrentCodeHash<T: Config> = StorageMap<_, Twox64Concat, ParaId, ValidationCodeHash>;

	/// Actual past code hash, indicated by the para id as well as the block number at which it
	/// became outdated.
	///
	/// Corresponding code can be retrieved with [`CodeByHash`].
	#[pallet::storage]
	pub(super) type PastCodeHash<T: Config> =
		StorageMap<_, Twox64Concat, (ParaId, BlockNumberFor<T>), ValidationCodeHash>;

	/// Past code of parachains. The parachains themselves may not be registered anymore,
	/// but we also keep their code on-chain for the same amount of time as outdated code
	/// to keep it available for approval checkers.
	#[pallet::storage]
	pub type PastCodeMeta<T: Config> =
		StorageMap<_, Twox64Concat, ParaId, ParaPastCodeMeta<BlockNumberFor<T>>, ValueQuery>;

	/// Which paras have past code that needs pruning and the relay-chain block at which the code
	/// was replaced. Note that this is the actual height of the included block, not the expected
	/// height at which the code upgrade would be applied, although they may be equal.
	/// This is to ensure the entire acceptance period is covered, not an offset acceptance period
	/// starting from the time at which the parachain perceives a code upgrade as having occurred.
	/// Multiple entries for a single para are permitted. Ordered ascending by block number.
	#[pallet::storage]
	pub(super) type PastCodePruning<T: Config> =
		StorageValue<_, Vec<(ParaId, BlockNumberFor<T>)>, ValueQuery>;

	/// The block number at which the planned code change is expected for a parachain.
	///
	/// The change will be applied after the first parablock for this ID included which executes
	/// in the context of a relay chain block with a number >= `expected_at`.
	#[pallet::storage]
	pub type FutureCodeUpgrades<T: Config> = StorageMap<_, Twox64Concat, ParaId, BlockNumberFor<T>>;

	/// The list of upcoming future code upgrades.
	///
	/// Each item is a pair of the parachain and the expected block at which the upgrade should be
	/// applied. The upgrade will be applied at the given relay chain block. In contrast to
	/// [`FutureCodeUpgrades`] this code upgrade will be applied regardless the parachain making any
	/// progress or not.
	///
	/// Ordered ascending by block number.
	#[pallet::storage]
	pub(super) type FutureCodeUpgradesAt<T: Config> =
		StorageValue<_, Vec<(ParaId, BlockNumberFor<T>)>, ValueQuery>;

	/// The actual future code hash of a para.
	///
	/// Corresponding code can be retrieved with [`CodeByHash`].
	#[pallet::storage]
	pub type FutureCodeHash<T: Config> = StorageMap<_, Twox64Concat, ParaId, ValidationCodeHash>;

	/// The code hash authorizations for a para which will expire `expire_at` `BlockNumberFor<T>`.
	#[pallet::storage]
	pub type AuthorizedCodeHash<T: Config> =
		StorageMap<_, Twox64Concat, ParaId, AuthorizedCodeHashAndExpiry<BlockNumberFor<T>>>;

	/// This is used by the relay-chain to communicate to a parachain a go-ahead with in the upgrade
	/// procedure.
	///
	/// This value is absent when there are no upgrades scheduled or during the time the relay chain
	/// performs the checks. It is set at the first relay-chain block when the corresponding
	/// parachain can switch its upgrade function. As soon as the parachain's block is included, the
	/// value gets reset to `None`.
	///
	/// NOTE that this field is used by parachains via merkle storage proofs, therefore changing
	/// the format will require migration of parachains.
	#[pallet::storage]
	pub(super) type UpgradeGoAheadSignal<T: Config> =
		StorageMap<_, Twox64Concat, ParaId, UpgradeGoAhead>;

	/// This is used by the relay-chain to communicate that there are restrictions for performing
	/// an upgrade for this parachain.
	///
	/// This may be a because the parachain waits for the upgrade cooldown to expire. Another
	/// potential use case is when we want to perform some maintenance (such as storage migration)
	/// we could restrict upgrades to make the process simpler.
	///
	/// NOTE that this field is used by parachains via merkle storage proofs, therefore changing
	/// the format will require migration of parachains.
	#[pallet::storage]
	pub type UpgradeRestrictionSignal<T: Config> =
		StorageMap<_, Twox64Concat, ParaId, UpgradeRestriction>;

	/// The list of parachains that are awaiting for their upgrade restriction to cooldown.
	///
	/// Ordered ascending by block number.
	#[pallet::storage]
	pub(super) type UpgradeCooldowns<T: Config> =
		StorageValue<_, Vec<(ParaId, BlockNumberFor<T>)>, ValueQuery>;

	/// The list of upcoming code upgrades.
	///
	/// Each item is a pair of which para performs a code upgrade and at which relay-chain block it
	/// is expected at.
	///
	/// Ordered ascending by block number.
	#[pallet::storage]
	pub(super) type UpcomingUpgrades<T: Config> =
		StorageValue<_, Vec<(ParaId, BlockNumberFor<T>)>, ValueQuery>;

	/// The actions to perform during the start of a specific session index.
	#[pallet::storage]
	pub type ActionsQueue<T: Config> =
		StorageMap<_, Twox64Concat, SessionIndex, Vec<ParaId>, ValueQuery>;

	/// Upcoming paras instantiation arguments.
	///
	/// NOTE that after PVF pre-checking is enabled the para genesis arg will have it's code set
	/// to empty. Instead, the code will be saved into the storage right away via `CodeByHash`.
	#[pallet::storage]
	pub(super) type UpcomingParasGenesis<T: Config> =
		StorageMap<_, Twox64Concat, ParaId, ParaGenesisArgs>;

	/// The number of reference on the validation code in [`CodeByHash`] storage.
	#[pallet::storage]
	pub(super) type CodeByHashRefs<T: Config> =
		StorageMap<_, Identity, ValidationCodeHash, u32, ValueQuery>;

	/// Validation code stored by its hash.
	///
	/// This storage is consistent with [`FutureCodeHash`], [`CurrentCodeHash`] and
	/// [`PastCodeHash`].
	#[pallet::storage]
	pub type CodeByHash<T: Config> = StorageMap<_, Identity, ValidationCodeHash, ValidationCode>;

	#[pallet::genesis_config]
	#[derive(DefaultNoBound)]
	pub struct GenesisConfig<T: Config> {
		#[serde(skip)]
		pub _config: core::marker::PhantomData<T>,
		pub paras: Vec<(ParaId, ParaGenesisArgs)>,
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			let mut parachains = ParachainsCache::new();
			for (id, genesis_args) in &self.paras {
				if genesis_args.validation_code.0.is_empty() {
					panic!("empty validation code is not allowed in genesis");
				}
				Pallet::<T>::initialize_para_now(&mut parachains, *id, genesis_args);
				if genesis_args.para_kind == ParaKind::Parachain {
					T::AssignCoretime::assign_coretime(*id)
						.expect("Assigning coretime works at genesis; qed");
				}
			}
			// parachains are flushed on drop
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set the storage for the parachain validation code immediately.
		#[pallet::call_index(0)]
		#[pallet::weight(<T as Config>::WeightInfo::force_set_current_code(new_code.0.len() as u32))]
		pub fn force_set_current_code(
			origin: OriginFor<T>,
			para: ParaId,
			new_code: ValidationCode,
		) -> DispatchResult {
			ensure_root(origin)?;
			Self::do_force_set_current_code_update(para, new_code);
			Ok(())
		}

		/// Set the storage for the current parachain head data immediately.
		#[pallet::call_index(1)]
		#[pallet::weight(<T as Config>::WeightInfo::force_set_current_head(new_head.0.len() as u32))]
		pub fn force_set_current_head(
			origin: OriginFor<T>,
			para: ParaId,
			new_head: HeadData,
		) -> DispatchResult {
			ensure_root(origin)?;
			Self::set_current_head(para, new_head);
			Ok(())
		}

		/// Schedule an upgrade as if it was scheduled in the given relay parent block.
		#[pallet::call_index(2)]
		#[pallet::weight(<T as Config>::WeightInfo::force_schedule_code_upgrade(new_code.0.len() as u32))]
		pub fn force_schedule_code_upgrade(
			origin: OriginFor<T>,
			para: ParaId,
			new_code: ValidationCode,
			relay_parent_number: BlockNumberFor<T>,
		) -> DispatchResult {
			ensure_root(origin)?;
			let config = configuration::ActiveConfig::<T>::get();
			Self::schedule_code_upgrade(
				para,
				new_code,
				relay_parent_number,
				&config,
				UpgradeStrategy::ApplyAtExpectedBlock,
			);
			Self::deposit_event(Event::CodeUpgradeScheduled(para));
			Ok(())
		}

		/// Note a new block head for para within the context of the current block.
		#[pallet::call_index(3)]
		#[pallet::weight(<T as Config>::WeightInfo::force_note_new_head(new_head.0.len() as u32))]
		pub fn force_note_new_head(
			origin: OriginFor<T>,
			para: ParaId,
			new_head: HeadData,
		) -> DispatchResult {
			ensure_root(origin)?;
			let now = frame_system::Pallet::<T>::block_number();
			Self::note_new_head(para, new_head, now);
			Self::deposit_event(Event::NewHeadNoted(para));
			Ok(())
		}

		/// Put a parachain directly into the next session's action queue.
		/// We can't queue it any sooner than this without going into the
		/// initializer...
		#[pallet::call_index(4)]
		#[pallet::weight(<T as Config>::WeightInfo::force_queue_action())]
		pub fn force_queue_action(origin: OriginFor<T>, para: ParaId) -> DispatchResult {
			ensure_root(origin)?;
			let next_session = shared::CurrentSessionIndex::<T>::get().saturating_add(One::one());
			ActionsQueue::<T>::mutate(next_session, |v| {
				if let Err(i) = v.binary_search(&para) {
					v.insert(i, para);
				}
			});
			Self::deposit_event(Event::ActionQueued(para, next_session));
			Ok(())
		}

		/// Adds the validation code to the storage.
		///
		/// The code will not be added if it is already present. Additionally, if PVF pre-checking
		/// is running for that code, it will be instantly accepted.
		///
		/// Otherwise, the code will be added into the storage. Note that the code will be added
		/// into storage with reference count 0. This is to account the fact that there are no users
		/// for this code yet. The caller will have to make sure that this code eventually gets
		/// used by some parachain or removed from the storage to avoid storage leaks. For the
		/// latter prefer to use the `poke_unused_validation_code` dispatchable to raw storage
		/// manipulation.
		///
		/// This function is mainly meant to be used for upgrading parachains that do not follow
		/// the go-ahead signal while the PVF pre-checking feature is enabled.
		#[pallet::call_index(5)]
		#[pallet::weight(<T as Config>::WeightInfo::add_trusted_validation_code(validation_code.0.len() as u32))]
		pub fn add_trusted_validation_code(
			origin: OriginFor<T>,
			validation_code: ValidationCode,
		) -> DispatchResult {
			ensure_root(origin)?;
			let code_hash = validation_code.hash();

			if let Some(vote) = PvfActiveVoteMap::<T>::get(&code_hash) {
				// Remove the existing vote.
				PvfActiveVoteMap::<T>::remove(&code_hash);
				PvfActiveVoteList::<T>::mutate(|l| {
					if let Ok(i) = l.binary_search(&code_hash) {
						l.remove(i);
					}
				});

				let cfg = configuration::ActiveConfig::<T>::get();
				Self::enact_pvf_accepted(
					frame_system::Pallet::<T>::block_number(),
					&code_hash,
					&vote.causes,
					vote.age,
					&cfg,
				);
				return Ok(())
			}

			if CodeByHash::<T>::contains_key(&code_hash) {
				// There is no vote, but the code exists. Nothing to do here.
				return Ok(())
			}

			// At this point the code is unknown and there is no PVF pre-checking vote for it, so we
			// can just add the code into the storage.
			//
			// NOTE That we do not use `increase_code_ref` here, because the code is not yet used
			// by any parachain.
			CodeByHash::<T>::insert(code_hash, &validation_code);

			Ok(())
		}

		/// Remove the validation code from the storage iff the reference count is 0.
		///
		/// This is better than removing the storage directly, because it will not remove the code
		/// that was suddenly got used by some parachain while this dispatchable was pending
		/// dispatching.
		#[pallet::call_index(6)]
		#[pallet::weight(<T as Config>::WeightInfo::poke_unused_validation_code())]
		pub fn poke_unused_validation_code(
			origin: OriginFor<T>,
			validation_code_hash: ValidationCodeHash,
		) -> DispatchResult {
			ensure_root(origin)?;
			if CodeByHashRefs::<T>::get(&validation_code_hash) == 0 {
				CodeByHash::<T>::remove(&validation_code_hash);
			}
			Ok(())
		}

		/// Includes a statement for a PVF pre-checking vote. Potentially, finalizes the vote and
		/// enacts the results if that was the last vote before achieving the supermajority.
		#[pallet::call_index(7)]
		#[pallet::weight(
			<T as Config>::WeightInfo::include_pvf_check_statement_finalize_upgrade_accept()
				.max(<T as Config>::WeightInfo::include_pvf_check_statement_finalize_upgrade_reject())
				.max(<T as Config>::WeightInfo::include_pvf_check_statement_finalize_onboarding_accept()
					.max(<T as Config>::WeightInfo::include_pvf_check_statement_finalize_onboarding_reject())
				)
		)]
		pub fn include_pvf_check_statement(
			origin: OriginFor<T>,
			stmt: PvfCheckStatement,
			signature: ValidatorSignature,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;

			let validators = shared::ActiveValidatorKeys::<T>::get();
			let current_session = shared::CurrentSessionIndex::<T>::get();
			if stmt.session_index < current_session {
				return Err(Error::<T>::PvfCheckStatementStale.into())
			} else if stmt.session_index > current_session {
				return Err(Error::<T>::PvfCheckStatementFuture.into())
			}
			let validator_index = stmt.validator_index.0 as usize;
			let validator_public = validators
				.get(validator_index)
				.ok_or(Error::<T>::PvfCheckValidatorIndexOutOfBounds)?;

			let signing_payload = stmt.signing_payload();
			ensure!(
				signature.verify(&signing_payload[..], &validator_public),
				Error::<T>::PvfCheckInvalidSignature,
			);

			let mut active_vote = PvfActiveVoteMap::<T>::get(&stmt.subject)
				.ok_or(Error::<T>::PvfCheckSubjectInvalid)?;

			// Ensure that the validator submitting this statement hasn't voted already.
			ensure!(
				!active_vote
					.has_vote(validator_index)
					.ok_or(Error::<T>::PvfCheckValidatorIndexOutOfBounds)?,
				Error::<T>::PvfCheckDoubleVote,
			);

			// Finally, cast the vote and persist.
			if stmt.accept {
				active_vote.votes_accept.set(validator_index, true);
			} else {
				active_vote.votes_reject.set(validator_index, true);
			}

			if let Some(outcome) = active_vote.quorum(validators.len()) {
				// The quorum has been achieved.
				//
				// Remove the PVF vote from the active map and finalize the PVF checking according
				// to the outcome.
				PvfActiveVoteMap::<T>::remove(&stmt.subject);
				PvfActiveVoteList::<T>::mutate(|l| {
					if let Ok(i) = l.binary_search(&stmt.subject) {
						l.remove(i);
					}
				});
				match outcome {
					PvfCheckOutcome::Accepted => {
						let cfg = configuration::ActiveConfig::<T>::get();
						Self::enact_pvf_accepted(
							frame_system::Pallet::<T>::block_number(),
							&stmt.subject,
							&active_vote.causes,
							active_vote.age,
							&cfg,
						);
					},
					PvfCheckOutcome::Rejected => {
						Self::enact_pvf_rejected(&stmt.subject, active_vote.causes);
					},
				}

				// No weight refund since this statement was the last one and lead to finalization.
				Ok(().into())
			} else {
				// No quorum has been achieved.
				//
				// - So just store the updated state back into the storage.
				// - Only charge weight for simple vote inclusion.
				PvfActiveVoteMap::<T>::insert(&stmt.subject, active_vote);
				Ok(Some(<T as Config>::WeightInfo::include_pvf_check_statement()).into())
			}
		}

		/// Set the storage for the current parachain head data immediately.
		#[pallet::call_index(8)]
		#[pallet::weight(<T as Config>::WeightInfo::force_set_most_recent_context())]
		pub fn force_set_most_recent_context(
			origin: OriginFor<T>,
			para: ParaId,
			context: BlockNumberFor<T>,
		) -> DispatchResult {
			ensure_root(origin)?;
			MostRecentContext::<T>::insert(&para, context);
			Ok(())
		}

		/// Remove an upgrade cooldown for a parachain.
		///
		/// The cost for removing the cooldown earlier depends on the time left for the cooldown
		/// multiplied by [`Config::CooldownRemovalMultiplier`]. The paid tokens are burned.
		#[pallet::call_index(9)]
		#[pallet::weight(<T as Config>::WeightInfo::remove_upgrade_cooldown())]
		pub fn remove_upgrade_cooldown(origin: OriginFor<T>, para: ParaId) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let removed = UpgradeCooldowns::<T>::mutate(|cooldowns| {
				let Some(pos) = cooldowns.iter().position(|(p, _)| p == &para) else {
					return Ok::<_, DispatchError>(false)
				};
				let (_, cooldown_until) = cooldowns.remove(pos);

				let cost = Self::calculate_remove_upgrade_cooldown_cost(cooldown_until);

				// burn...
				T::Fungible::burn_from(
					&who,
					cost,
					Preservation::Preserve,
					Precision::Exact,
					Fortitude::Polite,
				)?;

				Ok(true)
			})?;

			if removed {
				UpgradeRestrictionSignal::<T>::remove(para);

				Self::deposit_event(Event::UpgradeCooldownRemoved { para_id: para });
			}

			Ok(())
		}

		/// Sets the storage for the authorized current code hash of the parachain.
		/// If not applied, it will be removed at the `System::block_number() + valid_period` block.
		///
		/// This can be useful, when triggering `Paras::force_set_current_code(para, code)`
		/// from a different chain than the one where the `Paras` pallet is deployed.
		///
		/// The main purpose is to avoid transferring the entire `code` Wasm blob between chains.
		/// Instead, we authorize `code_hash` with `root`, which can later be applied by
		/// `Paras::apply_authorized_force_set_current_code(para, code)` by anyone.
		///
		/// Authorizations are stored in an **overwriting manner**.
		#[pallet::call_index(10)]
		#[pallet::weight(<T as Config>::WeightInfo::authorize_force_set_current_code_hash())]
		pub fn authorize_force_set_current_code_hash(
			origin: OriginFor<T>,
			para: ParaId,
			new_code_hash: ValidationCodeHash,
			valid_period: BlockNumberFor<T>,
		) -> DispatchResult {
			T::AuthorizeCurrentCodeOrigin::ensure_origin(origin, &para)?;

			let now = frame_system::Pallet::<T>::block_number();
			let expire_at = now.saturating_add(valid_period);

			// insert authorized code hash and make sure to overwrite existing one for a para.
			AuthorizedCodeHash::<T>::insert(
				&para,
				AuthorizedCodeHashAndExpiry::from((new_code_hash, expire_at)),
			);
			Self::deposit_event(Event::CodeAuthorized {
				para_id: para,
				code_hash: new_code_hash,
				expire_at,
			});

			Ok(())
		}

		/// Applies the already authorized current code for the parachain,
		/// triggering the same functionality as `force_set_current_code`.
		#[pallet::call_index(11)]
		#[pallet::weight(<T as Config>::WeightInfo::apply_authorized_force_set_current_code(new_code.0.len() as u32))]
		pub fn apply_authorized_force_set_current_code(
			_origin: OriginFor<T>,
			para: ParaId,
			new_code: ValidationCode,
		) -> DispatchResultWithPostInfo {
			// no need to ensure, anybody can do this

			// Ensure `new_code` is authorized
			let _ = Self::validate_code_is_authorized(&new_code, &para)?;
			// Remove authorization
			AuthorizedCodeHash::<T>::remove(para);

			// apply/dispatch
			Self::do_force_set_current_code_update(para, new_code);

			Ok(Pays::No.into())
		}
	}

	impl<T: Config> Pallet<T> {
		pub(crate) fn calculate_remove_upgrade_cooldown_cost(
			cooldown_until: BlockNumberFor<T>,
		) -> BalanceOf<T> {
			let time_left =
				cooldown_until.saturating_sub(frame_system::Pallet::<T>::block_number());

			BalanceOf::<T>::from(time_left).saturating_mul(T::CooldownRemovalMultiplier::get())
		}
	}

	#[pallet::view_functions]
	impl<T: Config> Pallet<T> {
		/// Returns the cost for removing an upgrade cooldown for the given `para`.
		pub fn remove_upgrade_cooldown_cost(para: ParaId) -> BalanceOf<T> {
			UpgradeCooldowns::<T>::get()
				.iter()
				.find(|(p, _)| p == &para)
				.map(|(_, c)| Self::calculate_remove_upgrade_cooldown_cost(*c))
				.unwrap_or_default()
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;

		fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			match call {
				Call::include_pvf_check_statement { stmt, signature } => {
					let current_session = shared::CurrentSessionIndex::<T>::get();
					if stmt.session_index < current_session {
						return InvalidTransaction::Stale.into()
					} else if stmt.session_index > current_session {
						return InvalidTransaction::Future.into()
					}

					let validator_index = stmt.validator_index.0 as usize;
					let validators = shared::ActiveValidatorKeys::<T>::get();
					let validator_public = match validators.get(validator_index) {
						Some(pk) => pk,
						None =>
							return InvalidTransaction::Custom(INVALID_TX_BAD_VALIDATOR_IDX).into(),
					};

					let signing_payload = stmt.signing_payload();
					if !signature.verify(&signing_payload[..], &validator_public) {
						return InvalidTransaction::BadProof.into();
					}

					let active_vote = match PvfActiveVoteMap::<T>::get(&stmt.subject) {
						Some(v) => v,
						None => return InvalidTransaction::Custom(INVALID_TX_BAD_SUBJECT).into(),
					};

					match active_vote.has_vote(validator_index) {
						Some(false) => (),
						Some(true) =>
							return InvalidTransaction::Custom(INVALID_TX_DOUBLE_VOTE).into(),
						None =>
							return InvalidTransaction::Custom(INVALID_TX_BAD_VALIDATOR_IDX).into(),
					}

					ValidTransaction::with_tag_prefix("PvfPreCheckingVote")
						.priority(T::UnsignedPriority::get())
						.longevity(
							TryInto::<u64>::try_into(
								T::NextSessionRotation::average_session_length() / 2u32.into(),
							)
							.unwrap_or(64_u64),
						)
						.and_provides((stmt.session_index, stmt.validator_index, stmt.subject))
						.propagate(true)
						.build()
				},
				Call::apply_authorized_force_set_current_code { para, new_code } =>
					match Self::validate_code_is_authorized(new_code, para) {
						Ok(authorized_code) => {
							let now = frame_system::Pallet::<T>::block_number();
							let longevity = authorized_code.expire_at.saturating_sub(now);

							ValidTransaction::with_tag_prefix("ApplyAuthorizedForceSetCurrentCode")
								.priority(T::UnsignedPriority::get())
								.longevity(TryInto::<u64>::try_into(longevity).unwrap_or(64_u64))
								.and_provides((para, authorized_code.code_hash))
								.propagate(true)
								.build()
						},
						Err(_) =>
							return InvalidTransaction::Custom(INVALID_TX_UNAUTHORIZED_CODE).into(),
					},
				_ => InvalidTransaction::Call.into(),
			}
		}

		fn pre_dispatch(_call: &Self::Call) -> Result<(), TransactionValidityError> {
			// Return `Ok` here meaning that as soon as the transaction got into the block, it will
			// always dispatched. This is OK, since the `include_pvf_check_statement` dispatchable
			// will perform the same checks anyway, so there is no point doing it here.
			//
			// On the other hand, if we did not provide the implementation, then the default
			// implementation would be used. The default implementation just delegates the
			// pre-dispatch validation to `validate_unsigned`.
			Ok(())
		}
	}
}

// custom transaction error codes
const INVALID_TX_BAD_VALIDATOR_IDX: u8 = 1;
const INVALID_TX_BAD_SUBJECT: u8 = 2;
const INVALID_TX_DOUBLE_VOTE: u8 = 3;
const INVALID_TX_UNAUTHORIZED_CODE: u8 = 4;

/// This is intermediate "fix" for this issue:
/// <https://github.com/paritytech/polkadot-sdk/issues/4737>
///
/// It does not actually fix it, but makes the worst case better. Without that limit someone
/// could completely DoS the relay chain by registering a ridiculously high amount of paras.
/// With this limit the same attack could lead to some parachains ceasing to being able to
/// communicate via offchain XCMP. Snowbridge will still work as it only cares about `BridgeHub`.
pub const MAX_PARA_HEADS: usize = 1024;

impl<T: Config> Pallet<T> {
	/// This is a call to schedule code upgrades for parachains which is safe to be called
	/// outside of this module. That means this function does all checks necessary to ensure
	/// that some external code is allowed to trigger a code upgrade. We do not do auth checks,
	/// that should be handled by whomever calls this function.
	pub(crate) fn schedule_code_upgrade_external(
		id: ParaId,
		new_code: ValidationCode,
		upgrade_strategy: UpgradeStrategy,
	) -> DispatchResult {
		// Check that we can schedule an upgrade at all.
		ensure!(Self::can_upgrade_validation_code(id), Error::<T>::CannotUpgradeCode);
		let config = configuration::ActiveConfig::<T>::get();
		// Validation code sanity checks:
		ensure!(new_code.0.len() >= MIN_CODE_SIZE as usize, Error::<T>::InvalidCode);
		ensure!(new_code.0.len() <= config.max_code_size as usize, Error::<T>::InvalidCode);

		let current_block = frame_system::Pallet::<T>::block_number();
		// Schedule the upgrade with a delay just like if a parachain triggered the upgrade.
		let upgrade_block = current_block.saturating_add(config.validation_upgrade_delay);
		Self::schedule_code_upgrade(id, new_code, upgrade_block, &config, upgrade_strategy);
		Self::deposit_event(Event::CodeUpgradeScheduled(id));
		Ok(())
	}

	/// Set the current head of a parachain.
	pub(crate) fn set_current_head(para: ParaId, new_head: HeadData) {
		Heads::<T>::insert(&para, new_head);
		Self::deposit_event(Event::CurrentHeadUpdated(para));
	}

	/// Called by the initializer to initialize the paras pallet.
	pub(crate) fn initializer_initialize(now: BlockNumberFor<T>) -> Weight {
		Self::prune_old_code(now) +
			Self::process_scheduled_upgrade_changes(now) +
			Self::process_future_code_upgrades_at(now) +
			Self::prune_expired_authorizations(now)
	}

	/// Called by the initializer to finalize the paras pallet.
	pub(crate) fn initializer_finalize(now: BlockNumberFor<T>) {
		Self::process_scheduled_upgrade_cooldowns(now);
	}

	/// Called by the initializer to note that a new session has started.
	///
	/// Returns the list of outgoing paras from the actions queue.
	pub(crate) fn initializer_on_new_session(
		notification: &SessionChangeNotification<BlockNumberFor<T>>,
	) -> Vec<ParaId> {
		let outgoing_paras = Self::apply_actions_queue(notification.session_index);
		Self::groom_ongoing_pvf_votes(&notification.new_config, notification.validators.len());
		outgoing_paras
	}

	/// The validation code of live para.
	pub(crate) fn current_code(para_id: &ParaId) -> Option<ValidationCode> {
		CurrentCodeHash::<T>::get(para_id).and_then(|code_hash| {
			let code = CodeByHash::<T>::get(&code_hash);
			if code.is_none() {
				log::error!(
					"Pallet paras storage is inconsistent, code not found for hash {}",
					code_hash,
				);
				debug_assert!(false, "inconsistent paras storages");
			}
			code
		})
	}

	/// Get a list of the first [`MAX_PARA_HEADS`] para heads sorted by para_id.
	/// This method is likely to be removed in the future.
	pub fn sorted_para_heads() -> Vec<(u32, Vec<u8>)> {
		let mut heads: Vec<(u32, Vec<u8>)> =
			Heads::<T>::iter().map(|(id, head)| (id.into(), head.0)).collect();
		heads.sort_by_key(|(id, _)| *id);
		heads.truncate(MAX_PARA_HEADS);
		heads
	}

	// Apply all para actions queued for the given session index.
	//
	// The actions to take are based on the lifecycle of of the paras.
	//
	// The final state of any para after the actions queue should be as a
	// lease holding parachain, on-demand parachain, or not registered. (stable states)
	//
	// Returns the list of outgoing paras from the actions queue.
	fn apply_actions_queue(session: SessionIndex) -> Vec<ParaId> {
		let actions = ActionsQueue::<T>::take(session);
		let mut parachains = ParachainsCache::new();
		let now = frame_system::Pallet::<T>::block_number();
		let mut outgoing = Vec::new();

		for para in actions {
			let lifecycle = ParaLifecycles::<T>::get(&para);
			match lifecycle {
				None | Some(ParaLifecycle::Parathread) | Some(ParaLifecycle::Parachain) => { /* Nothing to do... */
				},
				Some(ParaLifecycle::Onboarding) => {
					if let Some(genesis_data) = UpcomingParasGenesis::<T>::take(&para) {
						Self::initialize_para_now(&mut parachains, para, &genesis_data);
					}
				},
				// Upgrade an on-demand parachain to a lease holding parachain
				Some(ParaLifecycle::UpgradingParathread) => {
					parachains.add(para);
					ParaLifecycles::<T>::insert(&para, ParaLifecycle::Parachain);
				},
				// Downgrade a lease holding parachain to an on-demand parachain
				Some(ParaLifecycle::DowngradingParachain) => {
					parachains.remove(para);
					ParaLifecycles::<T>::insert(&para, ParaLifecycle::Parathread);
				},
				// Offboard a lease holding or on-demand parachain from the system
				Some(ParaLifecycle::OffboardingParachain) |
				Some(ParaLifecycle::OffboardingParathread) => {
					parachains.remove(para);

					Heads::<T>::remove(&para);
					MostRecentContext::<T>::remove(&para);
					FutureCodeUpgrades::<T>::remove(&para);
					UpgradeGoAheadSignal::<T>::remove(&para);
					UpgradeRestrictionSignal::<T>::remove(&para);
					ParaLifecycles::<T>::remove(&para);
					let removed_future_code_hash = FutureCodeHash::<T>::take(&para);
					if let Some(removed_future_code_hash) = removed_future_code_hash {
						Self::decrease_code_ref(&removed_future_code_hash);
					}

					let removed_code_hash = CurrentCodeHash::<T>::take(&para);
					if let Some(removed_code_hash) = removed_code_hash {
						Self::note_past_code(para, now, now, removed_code_hash);
					}

					outgoing.push(para);
				},
			}
		}

		if !outgoing.is_empty() {
			// Filter offboarded parachains from the upcoming upgrades and upgrade cooldowns list.
			//
			// We do it after the offboarding to get away with only a single read/write per list.
			//
			// NOTE both of those iterates over the list and the outgoing. We do not expect either
			//      of these to be large. Thus should be fine.
			UpcomingUpgrades::<T>::mutate(|upcoming_upgrades| {
				upcoming_upgrades.retain(|(para, _)| !outgoing.contains(para));
			});
			UpgradeCooldowns::<T>::mutate(|upgrade_cooldowns| {
				upgrade_cooldowns.retain(|(para, _)| !outgoing.contains(para));
			});
			FutureCodeUpgradesAt::<T>::mutate(|future_upgrades| {
				future_upgrades.retain(|(para, _)| !outgoing.contains(para));
			});
		}

		// Persist parachains into the storage explicitly.
		drop(parachains);

		outgoing
	}

	// note replacement of the code of para with given `id`, which occurred in the
	// context of the given relay-chain block number. provide the replaced code.
	//
	// `at` for para-triggered replacement is the block number of the relay-chain
	// block in whose context the parablock was executed
	// (i.e. number of `relay_parent` in the receipt)
	fn note_past_code(
		id: ParaId,
		at: BlockNumberFor<T>,
		now: BlockNumberFor<T>,
		old_code_hash: ValidationCodeHash,
	) -> Weight {
		PastCodeMeta::<T>::mutate(&id, |past_meta| {
			past_meta.note_replacement(at, now);
		});

		PastCodeHash::<T>::insert(&(id, at), old_code_hash);

		// Schedule pruning for this past-code to be removed as soon as it
		// exits the slashing window.
		PastCodePruning::<T>::mutate(|pruning| {
			let insert_idx =
				pruning.binary_search_by_key(&now, |&(_, b)| b).unwrap_or_else(|idx| idx);
			pruning.insert(insert_idx, (id, now));
		});

		T::DbWeight::get().reads_writes(2, 3)
	}

	// looks at old code metadata, compares them to the current acceptance window, and prunes those
	// that are too old.
	fn prune_old_code(now: BlockNumberFor<T>) -> Weight {
		let config = configuration::ActiveConfig::<T>::get();
		let code_retention_period = config.code_retention_period;
		if now <= code_retention_period {
			let weight = T::DbWeight::get().reads_writes(1, 0);
			return weight
		}

		// The height of any changes we no longer should keep around.
		let pruning_height = now - (code_retention_period + One::one());

		let pruning_tasks_done =
			PastCodePruning::<T>::mutate(|pruning_tasks: &mut Vec<(_, BlockNumberFor<T>)>| {
				let (pruning_tasks_done, pruning_tasks_to_do) = {
					// find all past code that has just exited the pruning window.
					let up_to_idx =
						pruning_tasks.iter().take_while(|&(_, at)| at <= &pruning_height).count();
					(up_to_idx, pruning_tasks.drain(..up_to_idx))
				};

				for (para_id, _) in pruning_tasks_to_do {
					let full_deactivate = PastCodeMeta::<T>::mutate(&para_id, |meta| {
						for pruned_repl_at in meta.prune_up_to(pruning_height) {
							let removed_code_hash =
								PastCodeHash::<T>::take(&(para_id, pruned_repl_at));

							if let Some(removed_code_hash) = removed_code_hash {
								Self::decrease_code_ref(&removed_code_hash);
							} else {
								log::warn!(
									target: LOG_TARGET,
									"Missing code for removed hash {:?}",
									removed_code_hash,
								);
							}
						}

						meta.is_empty() && Heads::<T>::get(&para_id).is_none()
					});

					// This parachain has been removed and now the vestigial code
					// has been removed from the state. clean up meta as well.
					if full_deactivate {
						PastCodeMeta::<T>::remove(&para_id);
					}
				}

				pruning_tasks_done as u64
			});

		// 1 read for the meta for each pruning task, 1 read for the config
		// 2 writes: updating the meta and pruning the code
		T::DbWeight::get().reads_writes(1 + pruning_tasks_done, 2 * pruning_tasks_done)
	}

	/// This function removes authorizations that have expired,
	/// meaning their `expire_at` block is less than or equal to the current block (`now`).
	fn prune_expired_authorizations(now: BlockNumberFor<T>) -> Weight {
		let mut weight = T::DbWeight::get().reads(1);
		let to_remove = AuthorizedCodeHash::<T>::iter().filter_map(
			|(para, AuthorizedCodeHashAndExpiry { expire_at, .. })| {
				if expire_at <= now {
					Some(para)
				} else {
					None
				}
			},
		);
		for para in to_remove {
			AuthorizedCodeHash::<T>::remove(&para);
			weight.saturating_accrue(T::DbWeight::get().writes(1));
		}

		weight
	}

	/// Process the future code upgrades that should be applied directly.
	///
	/// Upgrades that should not be applied directly are being processed in
	/// [`Self::process_scheduled_upgrade_changes`].
	fn process_future_code_upgrades_at(now: BlockNumberFor<T>) -> Weight {
		// account weight for `FutureCodeUpgradeAt::mutate`.
		let mut weight = T::DbWeight::get().reads_writes(1, 1);
		FutureCodeUpgradesAt::<T>::mutate(
			|upcoming_upgrades: &mut Vec<(ParaId, BlockNumberFor<T>)>| {
				let num = upcoming_upgrades.iter().take_while(|&(_, at)| at <= &now).count();
				for (id, expected_at) in upcoming_upgrades.drain(..num) {
					weight += T::DbWeight::get().reads_writes(1, 1);

					// Both should always be `Some` in this case, since a code upgrade is scheduled.
					let new_code_hash = if let Some(new_code_hash) = FutureCodeHash::<T>::take(&id)
					{
						new_code_hash
					} else {
						log::error!(target: LOG_TARGET, "Missing future code hash for {:?}", &id);
						continue
					};

					weight += Self::set_current_code(id, new_code_hash, expected_at);
				}
				num
			},
		);

		weight
	}

	/// Process the timers related to upgrades. Specifically, the upgrade go ahead signals toggle
	/// and the upgrade cooldown restrictions. However, this function does not actually unset
	/// the upgrade restriction, that will happen in the `initializer_finalize` function. However,
	/// this function does count the number of cooldown timers expired so that we can reserve weight
	/// for the `initializer_finalize` function.
	fn process_scheduled_upgrade_changes(now: BlockNumberFor<T>) -> Weight {
		// account weight for `UpcomingUpgrades::mutate`.
		let mut weight = T::DbWeight::get().reads_writes(1, 1);
		let upgrades_signaled = UpcomingUpgrades::<T>::mutate(
			|upcoming_upgrades: &mut Vec<(ParaId, BlockNumberFor<T>)>| {
				let num = upcoming_upgrades.iter().take_while(|&(_, at)| at <= &now).count();
				for (para, _) in upcoming_upgrades.drain(..num) {
					UpgradeGoAheadSignal::<T>::insert(&para, UpgradeGoAhead::GoAhead);
				}
				num
			},
		);
		weight += T::DbWeight::get().writes(upgrades_signaled as u64);

		// account weight for `UpgradeCooldowns::get`.
		weight += T::DbWeight::get().reads(1);
		let cooldowns_expired =
			UpgradeCooldowns::<T>::get().iter().take_while(|&(_, at)| at <= &now).count();

		// reserve weight for `initializer_finalize`:
		// - 1 read and 1 write for `UpgradeCooldowns::mutate`.
		// - 1 write per expired cooldown.
		weight += T::DbWeight::get().reads_writes(1, 1);
		weight += T::DbWeight::get().reads(cooldowns_expired as u64);

		weight
	}

	/// Actually perform unsetting the expired upgrade restrictions.
	///
	/// See `process_scheduled_upgrade_changes` for more details.
	fn process_scheduled_upgrade_cooldowns(now: BlockNumberFor<T>) {
		UpgradeCooldowns::<T>::mutate(
			|upgrade_cooldowns: &mut Vec<(ParaId, BlockNumberFor<T>)>| {
				// Remove all expired signals and also prune the cooldowns.
				upgrade_cooldowns.retain(|(para, at)| {
					if at <= &now {
						UpgradeRestrictionSignal::<T>::remove(&para);
						false
					} else {
						true
					}
				});
			},
		);
	}

	/// Goes over all PVF votes in progress, reinitializes ballots, increments ages and prunes the
	/// active votes that reached their time-to-live.
	fn groom_ongoing_pvf_votes(
		cfg: &configuration::HostConfiguration<BlockNumberFor<T>>,
		new_n_validators: usize,
	) -> Weight {
		let mut weight = T::DbWeight::get().reads(1);

		let potentially_active_votes = PvfActiveVoteList::<T>::get();

		// Initially empty list which contains all the PVF active votes that made it through this
		// session change.
		//
		// **Ordered** as well as `PvfActiveVoteList`.
		let mut actually_active_votes = Vec::with_capacity(potentially_active_votes.len());

		for vote_subject in potentially_active_votes {
			let mut vote_state = match PvfActiveVoteMap::<T>::take(&vote_subject) {
				Some(v) => v,
				None => {
					// This branch should never be reached. This is due to the fact that the set of
					// `PvfActiveVoteMap`'s keys is always equal to the set of items found in
					// `PvfActiveVoteList`.
					log::warn!(
						target: LOG_TARGET,
						"The PvfActiveVoteMap is out of sync with PvfActiveVoteList!",
					);
					debug_assert!(false);
					continue
				},
			};

			vote_state.age += 1;
			if vote_state.age < cfg.pvf_voting_ttl {
				weight += T::DbWeight::get().writes(1);
				vote_state.reinitialize_ballots(new_n_validators);
				PvfActiveVoteMap::<T>::insert(&vote_subject, vote_state);

				// push maintaining the original order.
				actually_active_votes.push(vote_subject);
			} else {
				// TTL is reached. Reject.
				weight += Self::enact_pvf_rejected(&vote_subject, vote_state.causes);
			}
		}

		weight += T::DbWeight::get().writes(1);
		PvfActiveVoteList::<T>::put(actually_active_votes);

		weight
	}

	fn enact_pvf_accepted(
		now: BlockNumberFor<T>,
		code_hash: &ValidationCodeHash,
		causes: &[PvfCheckCause<BlockNumberFor<T>>],
		sessions_observed: SessionIndex,
		cfg: &configuration::HostConfiguration<BlockNumberFor<T>>,
	) -> Weight {
		let mut weight = Weight::zero();
		for cause in causes {
			weight += T::DbWeight::get().reads_writes(3, 2);
			Self::deposit_event(Event::PvfCheckAccepted(*code_hash, cause.para_id()));

			match cause {
				PvfCheckCause::Onboarding(id) => {
					weight += Self::proceed_with_onboarding(*id, sessions_observed);
				},
				PvfCheckCause::Upgrade { id, included_at, upgrade_strategy } => {
					weight += Self::proceed_with_upgrade(
						*id,
						code_hash,
						now,
						*included_at,
						cfg,
						*upgrade_strategy,
					);
				},
			}
		}
		weight
	}

	fn proceed_with_onboarding(id: ParaId, sessions_observed: SessionIndex) -> Weight {
		let weight = T::DbWeight::get().reads_writes(2, 1);

		// we should onboard only after `SESSION_DELAY` sessions but we should take
		// into account the number of sessions the PVF pre-checking occupied.
		//
		// we cannot onboard at the current session, so it must be at least one
		// session ahead.
		let onboard_at: SessionIndex = shared::CurrentSessionIndex::<T>::get() +
			cmp::max(shared::SESSION_DELAY.saturating_sub(sessions_observed), 1);

		ActionsQueue::<T>::mutate(onboard_at, |v| {
			if let Err(i) = v.binary_search(&id) {
				v.insert(i, id);
			}
		});

		weight
	}

	fn proceed_with_upgrade(
		id: ParaId,
		code_hash: &ValidationCodeHash,
		now: BlockNumberFor<T>,
		relay_parent_number: BlockNumberFor<T>,
		cfg: &configuration::HostConfiguration<BlockNumberFor<T>>,
		upgrade_strategy: UpgradeStrategy,
	) -> Weight {
		let mut weight = Weight::zero();

		// Compute the relay-chain block number starting at which the code upgrade is ready to
		// be applied.
		//
		// The first parablock that has a relay-parent higher or at the same height of
		// `expected_at` will trigger the code upgrade. The parablock that comes after that will
		// be validated against the new validation code.
		//
		// Here we are trying to choose the block number that will have
		// `validation_upgrade_delay` blocks from the relay-parent of inclusion of the the block
		// that scheduled code upgrade but no less than `minimum_validation_upgrade_delay`. We
		// want this delay out of caution so that when the last vote for pre-checking comes the
		// parachain will have some time until the upgrade finally takes place.
		let expected_at = cmp::max(
			relay_parent_number + cfg.validation_upgrade_delay,
			now + cfg.minimum_validation_upgrade_delay,
		);

		match upgrade_strategy {
			UpgradeStrategy::ApplyAtExpectedBlock => {
				FutureCodeUpgradesAt::<T>::mutate(|future_upgrades| {
					let insert_idx = future_upgrades
						.binary_search_by_key(&expected_at, |&(_, b)| b)
						.unwrap_or_else(|idx| idx);
					future_upgrades.insert(insert_idx, (id, expected_at));
				});

				weight += T::DbWeight::get().reads_writes(0, 2);
			},
			UpgradeStrategy::SetGoAheadSignal => {
				FutureCodeUpgrades::<T>::insert(&id, expected_at);

				UpcomingUpgrades::<T>::mutate(|upcoming_upgrades| {
					let insert_idx = upcoming_upgrades
						.binary_search_by_key(&expected_at, |&(_, b)| b)
						.unwrap_or_else(|idx| idx);
					upcoming_upgrades.insert(insert_idx, (id, expected_at));
				});

				weight += T::DbWeight::get().reads_writes(1, 3);
			},
		}

		let expected_at = expected_at.saturated_into();
		let log = ConsensusLog::ParaScheduleUpgradeCode(id, *code_hash, expected_at);
		frame_system::Pallet::<T>::deposit_log(log.into());

		weight
	}

	fn enact_pvf_rejected(
		code_hash: &ValidationCodeHash,
		causes: Vec<PvfCheckCause<BlockNumberFor<T>>>,
	) -> Weight {
		let mut weight = Weight::zero();

		for cause in causes {
			// Whenever PVF pre-checking is started or a new cause is added to it, the RC is bumped.
			// Now we need to unbump it.
			weight += Self::decrease_code_ref(code_hash);

			weight += T::DbWeight::get().reads_writes(3, 2);
			Self::deposit_event(Event::PvfCheckRejected(*code_hash, cause.para_id()));

			match cause {
				PvfCheckCause::Onboarding(id) => {
					// Here we need to undo everything that was done during
					// `schedule_para_initialize`. Essentially, the logic is similar to offboarding,
					// with exception that before actual onboarding the parachain did not have a
					// chance to reach to upgrades. Therefore we can skip all the upgrade related
					// storage items here.
					weight += T::DbWeight::get().writes(3);
					UpcomingParasGenesis::<T>::remove(&id);
					CurrentCodeHash::<T>::remove(&id);
					ParaLifecycles::<T>::remove(&id);
				},
				PvfCheckCause::Upgrade { id, .. } => {
					weight += T::DbWeight::get().writes(2);
					UpgradeGoAheadSignal::<T>::insert(&id, UpgradeGoAhead::Abort);
					FutureCodeHash::<T>::remove(&id);
				},
			}
		}

		weight
	}

	/// Verify that `schedule_para_initialize` can be called successfully.
	///
	/// Returns false if para is already registered in the system.
	pub fn can_schedule_para_initialize(id: &ParaId) -> bool {
		ParaLifecycles::<T>::get(id).is_none()
	}

	/// Schedule a para to be initialized. If the validation code is not already stored in the
	/// code storage, then a PVF pre-checking process will be initiated.
	///
	/// Only after the PVF pre-checking succeeds can the para be onboarded. Note, that calling this
	/// does not guarantee that the parachain will eventually be onboarded. This can happen in case
	/// the PVF does not pass PVF pre-checking.
	///
	/// The Para ID should be not activated in this pallet. The validation code supplied in
	/// `genesis_data` should not be empty. If those conditions are not met, then the para cannot
	/// be onboarded.
	pub(crate) fn schedule_para_initialize(
		id: ParaId,
		mut genesis_data: ParaGenesisArgs,
	) -> DispatchResult {
		// Make sure parachain isn't already in our system and that the onboarding parameters are
		// valid.
		ensure!(Self::can_schedule_para_initialize(&id), Error::<T>::CannotOnboard);
		ensure!(!genesis_data.validation_code.0.is_empty(), Error::<T>::CannotOnboard);
		ParaLifecycles::<T>::insert(&id, ParaLifecycle::Onboarding);

		// HACK: here we are doing something nasty.
		//
		// In order to fix the [soaking issue] we insert the code eagerly here. When the onboarding
		// is finally enacted, we do not need to insert the code anymore. Therefore, there is no
		// reason for the validation code to be copied into the `ParaGenesisArgs`. We also do not
		// want to risk it by copying the validation code needlessly to not risk adding more
		// memory pressure.
		//
		// That said, we also want to preserve `ParaGenesisArgs` as it is, for now. There are two
		// reasons:
		//
		// - Doing it within the context of the PR that introduces this change is undesirable, since
		//   it is already a big change, and that change would require a migration. Moreover, if we
		//   run the new version of the runtime, there will be less things to worry about during the
		//   eventual proper migration.
		//
		// - This data type already is used for generating genesis, and changing it will probably
		//   introduce some unnecessary burden.
		//
		// So instead of going through it right now, we will do something sneaky. Specifically:
		//
		// - Insert the `CurrentCodeHash` now, instead during the onboarding. That would allow to
		//   get rid of hashing of the validation code when onboarding.
		//
		// - Replace `validation_code` with a sentinel value: an empty vector. This should be fine
		//   as long we do not allow registering parachains with empty code. At the moment of
		//   writing this should already be the case.
		//
		// - Empty value is treated as the current code is already inserted during the onboarding.
		//
		// This is only an intermediate solution and should be fixed in foreseeable future.
		//
		// [soaking issue]: https://github.com/paritytech/polkadot/issues/3918
		let validation_code =
			mem::replace(&mut genesis_data.validation_code, ValidationCode(Vec::new()));
		UpcomingParasGenesis::<T>::insert(&id, genesis_data);
		let validation_code_hash = validation_code.hash();
		CurrentCodeHash::<T>::insert(&id, validation_code_hash);

		let cfg = configuration::ActiveConfig::<T>::get();
		Self::kick_off_pvf_check(
			PvfCheckCause::Onboarding(id),
			validation_code_hash,
			validation_code,
			&cfg,
		);

		Ok(())
	}

	/// Schedule a para to be cleaned up at the start of the next session.
	///
	/// Will return error if either is true:
	///
	/// - para is not a stable parachain (i.e. [`ParaLifecycle::is_stable`] is `false`)
	/// - para has a pending upgrade.
	/// - para has unprocessed messages in its UMP queue.
	///
	/// No-op if para is not registered at all.
	pub(crate) fn schedule_para_cleanup(id: ParaId) -> DispatchResult {
		// Disallow offboarding in case there is a PVF pre-checking in progress.
		//
		// This is not a fundamental limitation but rather simplification: it allows us to get
		// away without introducing additional logic for pruning and, more importantly, enacting
		// ongoing PVF pre-checking votes. It also removes some nasty edge cases.
		//
		// However, an upcoming upgrade on its own imposes no restrictions. An upgrade is enacted
		// with a new para head, so if a para never progresses we still should be able to offboard
		// it.
		//
		// This implicitly assumes that the given para exists, i.e. it's lifecycle != None.
		if let Some(future_code_hash) = FutureCodeHash::<T>::get(&id) {
			let active_prechecking = PvfActiveVoteList::<T>::get();
			if active_prechecking.contains(&future_code_hash) {
				return Err(Error::<T>::CannotOffboard.into())
			}
		}

		let lifecycle = ParaLifecycles::<T>::get(&id);
		match lifecycle {
			// If para is not registered, nothing to do!
			None => return Ok(()),
			Some(ParaLifecycle::Parathread) => {
				ParaLifecycles::<T>::insert(&id, ParaLifecycle::OffboardingParathread);
			},
			Some(ParaLifecycle::Parachain) => {
				ParaLifecycles::<T>::insert(&id, ParaLifecycle::OffboardingParachain);
			},
			_ => return Err(Error::<T>::CannotOffboard.into()),
		}

		let scheduled_session = Self::scheduled_session();
		ActionsQueue::<T>::mutate(scheduled_session, |v| {
			if let Err(i) = v.binary_search(&id) {
				v.insert(i, id);
			}
		});

		if <T as Config>::QueueFootprinter::message_count(UmpQueueId::Para(id)) != 0 {
			return Err(Error::<T>::CannotOffboard.into())
		}

		Ok(())
	}

	/// Schedule a parathread (on-demand parachain) to be upgraded to a lease holding parachain.
	///
	/// Will return error if `ParaLifecycle` is not `Parathread`.
	pub(crate) fn schedule_parathread_upgrade(id: ParaId) -> DispatchResult {
		let scheduled_session = Self::scheduled_session();
		let lifecycle = ParaLifecycles::<T>::get(&id).ok_or(Error::<T>::NotRegistered)?;

		ensure!(lifecycle == ParaLifecycle::Parathread, Error::<T>::CannotUpgrade);

		ParaLifecycles::<T>::insert(&id, ParaLifecycle::UpgradingParathread);
		ActionsQueue::<T>::mutate(scheduled_session, |v| {
			if let Err(i) = v.binary_search(&id) {
				v.insert(i, id);
			}
		});

		Ok(())
	}

	/// Schedule a lease holding parachain to be downgraded to an on-demand parachain.
	///
	/// Noop if `ParaLifecycle` is not `Parachain`.
	pub(crate) fn schedule_parachain_downgrade(id: ParaId) -> DispatchResult {
		let scheduled_session = Self::scheduled_session();
		let lifecycle = ParaLifecycles::<T>::get(&id).ok_or(Error::<T>::NotRegistered)?;

		ensure!(lifecycle == ParaLifecycle::Parachain, Error::<T>::CannotDowngrade);

		ParaLifecycles::<T>::insert(&id, ParaLifecycle::DowngradingParachain);
		ActionsQueue::<T>::mutate(scheduled_session, |v| {
			if let Err(i) = v.binary_search(&id) {
				v.insert(i, id);
			}
		});

		Ok(())
	}

	/// Schedule a future code upgrade of the given parachain.
	///
	/// If the new code is not known, then the PVF pre-checking will be started for that validation
	/// code. In case the validation code does not pass the PVF pre-checking process, the
	/// upgrade will be aborted.
	///
	/// Only after the code is approved by the process, the upgrade can be scheduled. Specifically,
	/// the relay-chain block number will be determined at which the upgrade will take place. We
	/// call that block `expected_at`.
	///
	/// Once the candidate with the relay-parent >= `expected_at` is enacted, the new validation
	/// code will be applied. Therefore, the new code will be used to validate the next candidate.
	///
	/// The new code should not be equal to the current one, otherwise the upgrade will be aborted.
	/// If there is already a scheduled code upgrade for the para, this is a no-op.
	///
	/// Inclusion block number specifies relay parent which enacted candidate initiating the
	/// upgrade.
	pub(crate) fn schedule_code_upgrade(
		id: ParaId,
		new_code: ValidationCode,
		inclusion_block_number: BlockNumberFor<T>,
		cfg: &configuration::HostConfiguration<BlockNumberFor<T>>,
		upgrade_strategy: UpgradeStrategy,
	) {
		// Should be prevented by checks in `schedule_code_upgrade_external`
		let new_code_len = new_code.0.len();
		if new_code_len < MIN_CODE_SIZE as usize || new_code_len > cfg.max_code_size as usize {
			log::warn!(target: LOG_TARGET, "attempted to schedule an upgrade with invalid new validation code",);
			return
		}

		// Enacting this should be prevented by the `can_upgrade_validation_code`
		if FutureCodeHash::<T>::contains_key(&id) {
			// This branch should never be reached. Signalling an upgrade is disallowed for a para
			// that already has one upgrade scheduled.
			//
			// Any candidate that attempts to do that should be rejected by
			// `can_upgrade_validation_code`.
			//
			// NOTE: we cannot set `UpgradeGoAheadSignal` signal here since this will be reset by
			//       the following call `note_new_head`
			log::warn!(target: LOG_TARGET, "ended up scheduling an upgrade while one is pending",);
			return
		}

		let code_hash = new_code.hash();

		// para signals an update to the same code? This does not make a lot of sense, so abort the
		// process right away.
		//
		// We do not want to allow this since it will mess with the code reference counting.
		if CurrentCodeHash::<T>::get(&id) == Some(code_hash) {
			// NOTE: we cannot set `UpgradeGoAheadSignal` signal here since this will be reset by
			//       the following call `note_new_head`
			log::warn!(
				target: LOG_TARGET,
				"para tried to upgrade to the same code. Abort the upgrade",
			);
			return
		}

		// This is the start of the upgrade process. Prevent any further attempts at upgrading.
		FutureCodeHash::<T>::insert(&id, &code_hash);
		UpgradeRestrictionSignal::<T>::insert(&id, UpgradeRestriction::Present);

		let next_possible_upgrade_at = inclusion_block_number + cfg.validation_upgrade_cooldown;
		UpgradeCooldowns::<T>::mutate(|upgrade_cooldowns| {
			let insert_idx = upgrade_cooldowns
				.binary_search_by_key(&next_possible_upgrade_at, |&(_, b)| b)
				.unwrap_or_else(|idx| idx);
			upgrade_cooldowns.insert(insert_idx, (id, next_possible_upgrade_at));
		});

		Self::kick_off_pvf_check(
			PvfCheckCause::Upgrade { id, included_at: inclusion_block_number, upgrade_strategy },
			code_hash,
			new_code,
			cfg,
		);
	}

	/// Makes sure that the given code hash has passed pre-checking.
	///
	/// If the given code hash has already passed pre-checking, then the approval happens
	/// immediately.
	///
	/// If the code is unknown, but the pre-checking for that PVF is already running then we perform
	/// "coalescing". We save the cause for this PVF pre-check request and just add it to the
	/// existing active PVF vote.
	///
	/// And finally, if the code is unknown and pre-checking is not running, we start the
	/// pre-checking process anew.
	///
	/// Unconditionally increases the reference count for the passed `code`.
	fn kick_off_pvf_check(
		cause: PvfCheckCause<BlockNumberFor<T>>,
		code_hash: ValidationCodeHash,
		code: ValidationCode,
		cfg: &configuration::HostConfiguration<BlockNumberFor<T>>,
	) -> Weight {
		let mut weight = Weight::zero();

		weight += T::DbWeight::get().reads_writes(3, 2);
		Self::deposit_event(Event::PvfCheckStarted(code_hash, cause.para_id()));

		weight += T::DbWeight::get().reads(1);
		match PvfActiveVoteMap::<T>::get(&code_hash) {
			None => {
				// We deliberately are using `CodeByHash` here instead of the `CodeByHashRefs`. This
				// is because the code may have been added by `add_trusted_validation_code`.
				let known_code = CodeByHash::<T>::contains_key(&code_hash);
				weight += T::DbWeight::get().reads(1);

				if known_code {
					// The code is known and there is no active PVF vote for it meaning it is
					// already checked -- fast track the PVF checking into the accepted state.
					weight += T::DbWeight::get().reads(1);
					let now = frame_system::Pallet::<T>::block_number();
					weight += Self::enact_pvf_accepted(now, &code_hash, &[cause], 0, cfg);
				} else {
					// PVF is not being pre-checked and it is not known. Start a new pre-checking
					// process.
					weight += T::DbWeight::get().reads_writes(3, 2);
					let now = frame_system::Pallet::<T>::block_number();
					let n_validators = shared::ActiveValidatorKeys::<T>::get().len();
					PvfActiveVoteMap::<T>::insert(
						&code_hash,
						PvfCheckActiveVoteState::new(now, n_validators, cause),
					);
					PvfActiveVoteList::<T>::mutate(|l| {
						if let Err(idx) = l.binary_search(&code_hash) {
							l.insert(idx, code_hash);
						}
					});
				}
			},
			Some(mut vote_state) => {
				// Coalescing: the PVF is already being pre-checked so we just need to piggy back
				// on it.
				weight += T::DbWeight::get().writes(1);
				vote_state.causes.push(cause);
				PvfActiveVoteMap::<T>::insert(&code_hash, vote_state);
			},
		}

		// We increase the code RC here in any case. Intuitively the parachain that requested this
		// action is now a user of that PVF.
		//
		// If the result of the pre-checking is reject, then we would decrease the RC for each
		// cause, including the current.
		//
		// If the result of the pre-checking is accept, then we do nothing to the RC because the PVF
		// will continue be used by the same users.
		//
		// If the PVF was fast-tracked (i.e. there is already non zero RC) and there is no
		// pre-checking, we also do not change the RC then.
		weight += Self::increase_code_ref(&code_hash, &code);

		weight
	}

	/// Note that a para has progressed to a new head, where the new head was executed in the
	/// context of a relay-chain block with given number. This will apply pending code upgrades
	/// based on the relay-parent block number provided.
	pub(crate) fn note_new_head(
		id: ParaId,
		new_head: HeadData,
		execution_context: BlockNumberFor<T>,
	) {
		Heads::<T>::insert(&id, &new_head);
		MostRecentContext::<T>::insert(&id, execution_context);

		if let Some(expected_at) = FutureCodeUpgrades::<T>::get(&id) {
			if expected_at <= execution_context {
				FutureCodeUpgrades::<T>::remove(&id);
				UpgradeGoAheadSignal::<T>::remove(&id);

				// Both should always be `Some` in this case, since a code upgrade is scheduled.
				let new_code_hash = if let Some(new_code_hash) = FutureCodeHash::<T>::take(&id) {
					new_code_hash
				} else {
					log::error!(target: LOG_TARGET, "Missing future code hash for {:?}", &id);
					return
				};

				Self::set_current_code(id, new_code_hash, expected_at);
			}
		} else {
			// This means there is no upgrade scheduled.
			//
			// In case the upgrade was aborted by the relay-chain we should reset
			// the `Abort` signal.
			UpgradeGoAheadSignal::<T>::remove(&id);
		};

		T::OnNewHead::on_new_head(id, &new_head);
	}

	/// Set the current code for the given parachain.
	// `at` for para-triggered replacement is the block number of the relay-chain
	// block in whose context the parablock was executed
	// (i.e. number of `relay_parent` in the receipt)
	pub(crate) fn set_current_code(
		id: ParaId,
		new_code_hash: ValidationCodeHash,
		at: BlockNumberFor<T>,
	) -> Weight {
		let maybe_prior_code_hash = CurrentCodeHash::<T>::get(&id);
		CurrentCodeHash::<T>::insert(&id, &new_code_hash);

		let log = ConsensusLog::ParaUpgradeCode(id, new_code_hash);
		<frame_system::Pallet<T>>::deposit_log(log.into());

		// `now` is only used for registering pruning as part of `fn note_past_code`
		let now = <frame_system::Pallet<T>>::block_number();

		let weight = if let Some(prior_code_hash) = maybe_prior_code_hash {
			Self::note_past_code(id, at, now, prior_code_hash)
		} else {
			log::error!(target: LOG_TARGET, "Missing prior code hash for para {:?}", &id);
			Weight::zero()
		};

		weight + T::DbWeight::get().writes(1)
	}

	/// Force set the current code for the given parachain.
	fn do_force_set_current_code_update(para: ParaId, new_code: ValidationCode) {
		let new_code_hash = new_code.hash();
		Self::increase_code_ref(&new_code_hash, &new_code);
		Self::set_current_code(para, new_code_hash, frame_system::Pallet::<T>::block_number());
		Self::deposit_event(Event::CurrentCodeUpdated(para));
	}

	/// Returns the list of PVFs (aka validation code) that require casting a vote by a validator in
	/// the active validator set.
	pub(crate) fn pvfs_require_precheck() -> Vec<ValidationCodeHash> {
		PvfActiveVoteList::<T>::get()
	}

	/// Submits a given PVF check statement with corresponding signature as an unsigned transaction
	/// into the memory pool. Ultimately, that disseminates the transaction across the network.
	///
	/// This function expects an offchain context and cannot be callable from the on-chain logic.
	///
	/// The signature assumed to pertain to `stmt`.
	pub(crate) fn submit_pvf_check_statement(
		stmt: PvfCheckStatement,
		signature: ValidatorSignature,
	) {
		use frame_system::offchain::SubmitTransaction;

		let xt = T::create_bare(Call::include_pvf_check_statement { stmt, signature }.into());
		if let Err(e) = SubmitTransaction::<T, Call<T>>::submit_transaction(xt) {
			log::error!(target: LOG_TARGET, "Error submitting pvf check statement: {:?}", e,);
		}
	}

	/// Returns the current lifecycle state of the para.
	pub fn lifecycle(id: ParaId) -> Option<ParaLifecycle> {
		ParaLifecycles::<T>::get(&id)
	}

	/// Returns whether the given ID refers to a valid para.
	///
	/// Paras that are onboarding or offboarding are not included.
	pub fn is_valid_para(id: ParaId) -> bool {
		if let Some(state) = ParaLifecycles::<T>::get(&id) {
			!state.is_onboarding() && !state.is_offboarding()
		} else {
			false
		}
	}

	/// Returns whether the given ID refers to a para that is offboarding.
	///
	/// An invalid or non-offboarding para ID will return `false`.
	pub fn is_offboarding(id: ParaId) -> bool {
		ParaLifecycles::<T>::get(&id).map_or(false, |state| state.is_offboarding())
	}

	/// Whether a para ID corresponds to any live lease holding parachain.
	///
	/// Includes lease holding parachains which will downgrade to a on-demand parachains in the
	/// future.
	pub fn is_parachain(id: ParaId) -> bool {
		if let Some(state) = ParaLifecycles::<T>::get(&id) {
			state.is_parachain()
		} else {
			false
		}
	}

	/// Whether a para ID corresponds to any live parathread (on-demand parachain).
	///
	/// Includes on-demand parachains which will upgrade to lease holding parachains in the future.
	pub fn is_parathread(id: ParaId) -> bool {
		if let Some(state) = ParaLifecycles::<T>::get(&id) {
			state.is_parathread()
		} else {
			false
		}
	}

	/// If a candidate from the specified parachain were submitted at the current block, this
	/// function returns if that candidate passes the acceptance criteria.
	pub(crate) fn can_upgrade_validation_code(id: ParaId) -> bool {
		FutureCodeHash::<T>::get(&id).is_none() && UpgradeRestrictionSignal::<T>::get(&id).is_none()
	}

	/// Return the session index that should be used for any future scheduled changes.
	fn scheduled_session() -> SessionIndex {
		shared::Pallet::<T>::scheduled_session()
	}

	/// Store the validation code if not already stored, and increase the number of reference.
	///
	/// Returns the weight consumed.
	fn increase_code_ref(code_hash: &ValidationCodeHash, code: &ValidationCode) -> Weight {
		let mut weight = T::DbWeight::get().reads_writes(1, 1);
		CodeByHashRefs::<T>::mutate(code_hash, |refs| {
			if *refs == 0 {
				weight += T::DbWeight::get().writes(1);
				CodeByHash::<T>::insert(code_hash, code);
			}
			*refs += 1;
		});
		weight
	}

	/// Decrease the number of reference of the validation code and remove it from storage if zero
	/// is reached.
	///
	/// Returns the weight consumed.
	fn decrease_code_ref(code_hash: &ValidationCodeHash) -> Weight {
		let mut weight = T::DbWeight::get().reads(1);
		let refs = CodeByHashRefs::<T>::get(code_hash);
		if refs == 0 {
			log::error!(target: LOG_TARGET, "Code refs is already zero for {:?}", code_hash);
			return weight
		}
		if refs <= 1 {
			weight += T::DbWeight::get().writes(2);
			CodeByHash::<T>::remove(code_hash);
			CodeByHashRefs::<T>::remove(code_hash);
		} else {
			weight += T::DbWeight::get().writes(1);
			CodeByHashRefs::<T>::insert(code_hash, refs - 1);
		}
		weight
	}

	/// Test function for triggering a new session in this pallet.
	#[cfg(any(feature = "std", feature = "runtime-benchmarks", test))]
	pub fn test_on_new_session() {
		Self::initializer_on_new_session(&SessionChangeNotification {
			session_index: shared::CurrentSessionIndex::<T>::get(),
			..Default::default()
		});
	}

	#[cfg(any(feature = "runtime-benchmarks", test))]
	pub fn heads_insert(para_id: &ParaId, head_data: HeadData) {
		Heads::<T>::insert(para_id, head_data);
	}

	/// A low-level function to eagerly initialize a given para.
	pub(crate) fn initialize_para_now(
		parachains: &mut ParachainsCache<T>,
		id: ParaId,
		genesis_data: &ParaGenesisArgs,
	) {
		match genesis_data.para_kind {
			ParaKind::Parachain => {
				parachains.add(id);
				ParaLifecycles::<T>::insert(&id, ParaLifecycle::Parachain);
			},
			ParaKind::Parathread => ParaLifecycles::<T>::insert(&id, ParaLifecycle::Parathread),
		}

		// HACK: see the notice in `schedule_para_initialize`.
		//
		// Apparently, this is left over from a prior version of the runtime.
		// To handle this we just insert the code and link the current code hash
		// to it.
		if !genesis_data.validation_code.0.is_empty() {
			let code_hash = genesis_data.validation_code.hash();
			Self::increase_code_ref(&code_hash, &genesis_data.validation_code);
			CurrentCodeHash::<T>::insert(&id, code_hash);
		}

		Heads::<T>::insert(&id, &genesis_data.genesis_head);
		MostRecentContext::<T>::insert(&id, BlockNumberFor::<T>::from(0u32));
	}

	#[cfg(test)]
	pub(crate) fn active_vote_state(
		code_hash: &ValidationCodeHash,
	) -> Option<PvfCheckActiveVoteState<BlockNumberFor<T>>> {
		PvfActiveVoteMap::<T>::get(code_hash)
	}

	/// This function checks whether the given `code.hash()` exists in the `AuthorizedCodeHash` map
	/// of authorized code hashes for a para. If found, it verifies that the associated code
	/// matches the provided `code`. If the validation is successful, it returns tuple as the
	/// authorized `ValidationCodeHash` with `expire_at`.
	pub(crate) fn validate_code_is_authorized(
		code: &ValidationCode,
		para: &ParaId,
	) -> Result<AuthorizedCodeHashAndExpiry<BlockNumberFor<T>>, Error<T>> {
		let authorized = AuthorizedCodeHash::<T>::get(para).ok_or(Error::<T>::NothingAuthorized)?;
		let now = frame_system::Pallet::<T>::block_number();
		ensure!(authorized.expire_at > now, Error::<T>::InvalidBlockNumber);
		ensure!(authorized.code_hash == code.hash(), Error::<T>::Unauthorized);
		Ok(authorized)
	}
}

/// An overlay over the `Parachains` storage entry that provides a convenient interface for adding
/// or removing parachains in bulk.
pub(crate) struct ParachainsCache<T: Config> {
	// `None` here means the parachains list has not been accessed yet, nevermind modified.
	parachains: Option<BTreeSet<ParaId>>,
	_config: PhantomData<T>,
}

impl<T: Config> ParachainsCache<T> {
	pub fn new() -> Self {
		Self { parachains: None, _config: PhantomData }
	}

	fn ensure_initialized(&mut self) -> &mut BTreeSet<ParaId> {
		self.parachains
			.get_or_insert_with(|| Parachains::<T>::get().into_iter().collect())
	}

	/// Adds the given para id to the list.
	pub fn add(&mut self, id: ParaId) {
		let parachains = self.ensure_initialized();
		parachains.insert(id);
	}

	/// Removes the given para id from the list of parachains. Does nothing if the id is not in the
	/// list.
	pub fn remove(&mut self, id: ParaId) {
		let parachains = self.ensure_initialized();
		parachains.remove(&id);
	}
}

impl<T: Config> Drop for ParachainsCache<T> {
	fn drop(&mut self) {
		if let Some(parachains) = self.parachains.take() {
			Parachains::<T>::put(parachains.into_iter().collect::<Vec<ParaId>>());
		}
	}
}
