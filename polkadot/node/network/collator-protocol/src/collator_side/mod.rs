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

use std::{
	collections::{HashMap, HashSet},
	time::Duration,
};

use bitvec::{bitvec, vec::BitVec};
use futures::{
	channel::oneshot, future::Fuse, pin_mut, select, stream::FuturesUnordered, FutureExt, StreamExt,
};
use metrics::{CollationStats, CollationTracker};
use schnellru::{ByLength, LruMap};
use sp_core::Pair;

use polkadot_node_network_protocol::{
	self as net_protocol,
	peer_set::{CollationVersion, PeerSet},
	request_response::{
		incoming::{self, OutgoingResponse},
		v2 as request_v2, IncomingRequestReceiver,
	},
	v1 as protocol_v1, v2 as protocol_v2, CollationProtocols, OurView, PeerId,
	UnifiedReputationChange as Rep, View,
};
use polkadot_node_primitives::{CollationSecondedSignal, PoV, Statement};
use polkadot_node_subsystem::{
	messages::{CollatorProtocolMessage, NetworkBridgeEvent, NetworkBridgeTxMessage},
	overseer, FromOrchestra, OverseerSignal,
};
use polkadot_node_subsystem_util::{
	backing_implicit_view::View as ImplicitView,
	reputation::{ReputationAggregator, REPUTATION_CHANGE_INTERVAL},
	runtime::{
		fetch_claim_queue, get_candidate_events, get_group_rotation_info, ClaimQueueSnapshot,
		RuntimeInfo,
	},
	TimeoutExt,
};
use polkadot_primitives::{
	vstaging::{CandidateEvent, CandidateReceiptV2 as CandidateReceipt},
	AuthorityDiscoveryId, BlockNumber, CandidateHash, CollatorPair, CoreIndex, GroupIndex, Hash,
	HeadData, Id as ParaId, SessionIndex,
};

use crate::{modify_reputation, LOG_TARGET, LOG_TARGET_STATS};

mod collation;
mod error;
mod metrics;
#[cfg(test)]
mod tests;
mod validators_buffer;

use collation::{
	ActiveCollationFetches, Collation, CollationSendResult, CollationStatus,
	VersionedCollationRequest, WaitingCollationFetches,
};
use error::{log_error, Error, FatalError, Result};
use validators_buffer::{
	ResetInterestTimeout, ValidatorGroupsBuffer, RESET_INTEREST_TIMEOUT, VALIDATORS_BUFFER_CAPACITY,
};

pub use metrics::Metrics;

const COST_INVALID_REQUEST: Rep = Rep::CostMajor("Peer sent unparsable request");
const COST_UNEXPECTED_MESSAGE: Rep = Rep::CostMinor("An unexpected message");
const COST_APPARENT_FLOOD: Rep =
	Rep::CostMinor("Message received when previous one was still being processed");

/// Time after starting an upload to a validator we will start another one to the next validator,
/// even if the upload was not finished yet.
///
/// This is to protect from a single slow validator preventing collations from happening.
///
/// For considerations on this value, see: https://github.com/paritytech/polkadot/issues/4386
const MAX_UNSHARED_UPLOAD_TIME: Duration = Duration::from_millis(150);

/// Ensure that collator updates its connection requests to validators
/// this long after the most recent leaf.
///
/// The timeout is designed for substreams to be properly closed if they need to be
/// reopened shortly after the next leaf.
///
/// Collators also update their connection requests on every new collation.
/// This timeout is mostly about removing stale connections while avoiding races
/// with new collations which may want to reactivate them.
///
/// Validators are obtained from [`ValidatorGroupsBuffer::validators_to_connect`].
const RECONNECT_AFTER_LEAF_TIMEOUT: Duration = Duration::from_secs(4);

/// Future that when resolved indicates that we should update reserved peer-set
/// of validators we want to be connected to.
///
/// `Pending` variant never finishes and should be used when there're no peers
/// connected.
type ReconnectTimeout = Fuse<futures_timer::Delay>;

#[derive(Debug)]
enum ShouldAdvertiseTo {
	Yes,
	NotAuthority,
	AlreadyAdvertised,
}

/// Info about validators we are currently connected to.
///
/// It keeps track to which validators we advertised our collation.
#[derive(Debug, Default)]
struct ValidatorGroup {
	/// Validators discovery ids. Lazily initialized when first
	/// distributing a collation.
	validators: Vec<AuthorityDiscoveryId>,

	/// Bits indicating which validators have already seen the announcement
	/// per candidate.
	advertised_to: HashMap<CandidateHash, BitVec>,
}

impl ValidatorGroup {
	/// Returns `true` if we should advertise our collation to the given peer.
	fn should_advertise_to(
		&self,
		candidate_hash: &CandidateHash,
		peer_ids: &HashMap<PeerId, HashSet<AuthorityDiscoveryId>>,
		peer: &PeerId,
	) -> ShouldAdvertiseTo {
		let authority_ids = match peer_ids.get(peer) {
			Some(authority_ids) => authority_ids,
			None => return ShouldAdvertiseTo::NotAuthority,
		};

		for id in authority_ids {
			// One peer id may correspond to different discovery ids across sessions,
			// having a non-empty intersection is sufficient to assume that this peer
			// belongs to this particular validator group.
			let validator_index = match self.validators.iter().position(|v| v == id) {
				Some(idx) => idx,
				None => continue,
			};

			// Either the candidate is unseen by this validator group
			// or the corresponding bit is not set.
			if self
				.advertised_to
				.get(candidate_hash)
				.map_or(true, |advertised| !advertised[validator_index])
			{
				return ShouldAdvertiseTo::Yes
			} else {
				return ShouldAdvertiseTo::AlreadyAdvertised
			}
		}

		ShouldAdvertiseTo::NotAuthority
	}

	/// Should be called after we advertised our collation to the given `peer` to keep track of it.
	fn advertised_to_peer(
		&mut self,
		candidate_hash: &CandidateHash,
		peer_ids: &HashMap<PeerId, HashSet<AuthorityDiscoveryId>>,
		peer: &PeerId,
	) {
		if let Some(authority_ids) = peer_ids.get(peer) {
			for id in authority_ids {
				let validator_index = match self.validators.iter().position(|v| v == id) {
					Some(idx) => idx,
					None => continue,
				};
				self.advertised_to
					.entry(*candidate_hash)
					.or_insert_with(|| bitvec![0; self.validators.len()])
					.set(validator_index, true);
			}
		}
	}
}

#[derive(Debug)]
struct PeerData {
	/// Peer's view.
	view: View,
	/// Unknown heads in the view.
	///
	/// This can happen when the validator is faster at importing a block and sending out its
	/// `View` than the collator is able to import a block.
	unknown_heads: LruMap<Hash, (), ByLength>,
}

/// A type wrapping a collation, it's designated core index and stats.
struct CollationData {
	collation: Collation,
	core_index: CoreIndex,
	stats: Option<CollationStats>,
}

impl CollationData {
	/// Returns inner collation ref.
	pub fn collation(&self) -> &Collation {
		&self.collation
	}

	/// Returns inner collation mut ref.
	pub fn collation_mut(&mut self) -> &mut Collation {
		&mut self.collation
	}

	/// Returns inner core index.
	pub fn core_index(&self) -> &CoreIndex {
		&self.core_index
	}

	/// Takes the stats and returns them.
	pub fn take_stats(&mut self) -> Option<CollationStats> {
		self.stats.take()
	}
}

struct PerRelayParent {
	/// Per core index validators group responsible for backing candidates built
	/// on top of this relay parent.
	validator_group: HashMap<CoreIndex, ValidatorGroup>,
	/// Distributed collations.
	collations: HashMap<CandidateHash, CollationData>,
	/// Number of assignments per core
	assignments: HashMap<CoreIndex, usize>,
	/// The relay parent block number
	block_number: Option<BlockNumber>,
}

impl PerRelayParent {
	fn new(
		para_id: ParaId,
		claim_queue: ClaimQueueSnapshot,
		block_number: Option<BlockNumber>,
	) -> Self {
		let assignments =
			claim_queue.iter_all_claims().fold(HashMap::new(), |mut acc, (core, claims)| {
				let n_claims = claims.iter().filter(|para| para == &&para_id).count();
				if n_claims > 0 {
					acc.insert(*core, n_claims);
				}
				acc
			});

		Self {
			validator_group: HashMap::default(),
			collations: HashMap::new(),
			assignments,
			block_number,
		}
	}
}

struct State {
	/// Our network peer id.
	local_peer_id: PeerId,

	/// Our collator pair.
	collator_pair: CollatorPair,

	/// The para this collator is collating on.
	/// Starts as `None` and is updated with every `CollateOn` message.
	collating_on: Option<ParaId>,

	/// Track all active peers and their views
	/// to determine what is relevant to them.
	peer_data: HashMap<PeerId, PeerData>,

	/// Leaves along with implicit ancestry.
	///
	/// It's `None` if the collator is not yet collating for a paraid.
	implicit_view: Option<ImplicitView>,

	/// Validators and distributed collations tracked for each relay parent from
	/// our view, including both leaves and implicit ancestry.
	per_relay_parent: HashMap<Hash, PerRelayParent>,

	/// The result senders per collation.
	collation_result_senders: HashMap<CandidateHash, oneshot::Sender<CollationSecondedSignal>>,

	/// The mapping from [`PeerId`] to [`HashSet<AuthorityDiscoveryId>`]. This is filled over time
	/// as we learn the [`PeerId`]'s by `PeerConnected` events.
	peer_ids: HashMap<PeerId, HashSet<AuthorityDiscoveryId>>,

	/// Tracks which validators we want to stay connected to.
	validator_groups_buf: ValidatorGroupsBuffer,

	/// Timeout-future which is reset after every leaf to [`RECONNECT_AFTER_LEAF_TIMEOUT`] seconds.
	/// When it fires, we update our reserved peers.
	reconnect_timeout: ReconnectTimeout,

	/// Metrics.
	metrics: Metrics,

	/// All collation fetching requests that are still waiting to be answered.
	///
	/// They are stored per relay parent, when our view changes and the relay parent moves out, we
	/// will cancel the fetch request.
	waiting_collation_fetches: HashMap<Hash, WaitingCollationFetches>,

	/// Active collation fetches.
	///
	/// Each future returns the relay parent of the finished collation fetch.
	active_collation_fetches: ActiveCollationFetches,

	/// Time limits for validators to fetch the collation once the advertisement
	/// was sent.
	///
	/// Given an implicit view a collation may stay in memory for significant amount
	/// of time, if we don't timeout validators the node will keep attempting to connect
	/// to unneeded peers.
	advertisement_timeouts: FuturesUnordered<ResetInterestTimeout>,

	/// Aggregated reputation change
	reputation: ReputationAggregator,

	/// An utility for tracking all collations produced by the collator.
	collation_tracker: CollationTracker,
}

impl State {
	/// Creates a new `State` instance with the given parameters and setting all remaining
	/// state fields to their default values (i.e. empty).
	fn new(
		local_peer_id: PeerId,
		collator_pair: CollatorPair,
		metrics: Metrics,
		reputation: ReputationAggregator,
	) -> State {
		State {
			local_peer_id,
			collator_pair,
			metrics,
			collating_on: Default::default(),
			peer_data: Default::default(),
			implicit_view: None,
			per_relay_parent: Default::default(),
			collation_result_senders: Default::default(),
			peer_ids: Default::default(),
			validator_groups_buf: ValidatorGroupsBuffer::with_capacity(VALIDATORS_BUFFER_CAPACITY),
			reconnect_timeout: Fuse::terminated(),
			waiting_collation_fetches: Default::default(),
			active_collation_fetches: Default::default(),
			advertisement_timeouts: Default::default(),
			reputation,
			collation_tracker: Default::default(),
		}
	}
}

/// Distribute a collation.
///
/// Figure out the core our para is assigned to and the relevant validators.
/// Issue a connection request to these validators.
/// If the para is not scheduled or next up on any core, at the relay-parent,
/// or the relay-parent isn't in the implicit ancestry, we ignore the message
/// as it must be invalid in that case - although this indicates a logic error
/// elsewhere in the node.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn distribute_collation<Context>(
	ctx: &mut Context,
	runtime: &mut RuntimeInfo,
	state: &mut State,
	id: ParaId,
	receipt: CandidateReceipt,
	pov: PoV,
	parent_head_data: HeadData,
	result_sender: Option<oneshot::Sender<CollationSecondedSignal>>,
	core_index: CoreIndex,
) -> Result<()> {
	let candidate_relay_parent = receipt.descriptor.relay_parent();
	let candidate_hash = receipt.hash();
	let cores_assigned = has_assigned_cores(&state.implicit_view, &state.per_relay_parent);

	let per_relay_parent = match state.per_relay_parent.get_mut(&candidate_relay_parent) {
		Some(per_relay_parent) => per_relay_parent,
		None => {
			gum::debug!(
				target: LOG_TARGET,
				para_id = %id,
				candidate_relay_parent = %candidate_relay_parent,
				candidate_hash = ?candidate_hash,
				"Candidate relay parent is out of our view",
			);
			return Ok(())
		},
	};

	let Some(collations_limit) = per_relay_parent.assignments.get(&core_index) else {
		gum::warn!(
			target: LOG_TARGET,
			para_id = %id,
			relay_parent = ?candidate_relay_parent,
			cores = ?per_relay_parent.assignments.keys(),
			?core_index,
			"Attempting to distribute collation for a core we are not assigned to ",
		);

		return Ok(())
	};

	let current_collations_count = per_relay_parent
		.collations
		.values()
		.filter(|c| c.core_index() == &core_index)
		.count();
	if current_collations_count >= *collations_limit {
		gum::debug!(
			target: LOG_TARGET,
			?candidate_relay_parent,
			"The limit of {} collations per relay parent for core {} is already reached",
			collations_limit,
			core_index.0,
		);
		return Ok(())
	}

	// We have already seen collation for this relay parent.
	if per_relay_parent.collations.contains_key(&candidate_hash) {
		gum::debug!(
			target: LOG_TARGET,
			?candidate_relay_parent,
			?candidate_hash,
			"Already seen this candidate",
		);
		return Ok(())
	}

	let elastic_scaling = per_relay_parent.assignments.len() > 1;
	if elastic_scaling {
		gum::debug!(
			target: LOG_TARGET,
			para_id = %id,
			cores = ?per_relay_parent.assignments.keys(),
			"{} is assigned to {} cores at {}", id, per_relay_parent.assignments.len(), candidate_relay_parent,
		);
	}

	let our_core = core_index;

	// Determine the group on that core.
	let GroupValidators { validators, session_index, group_index } =
		determine_our_validators(ctx, runtime, our_core, candidate_relay_parent).await?;

	if validators.is_empty() {
		gum::warn!(
			target: LOG_TARGET,
			core = ?our_core,
			"there are no validators assigned to core",
		);

		return Ok(())
	}

	// It's important to insert new collation interests **before**
	// issuing a connection request.
	//
	// If a validator managed to fetch all the relevant collations
	// but still assigned to our core, we keep the connection alive.
	state.validator_groups_buf.note_collation_advertised(
		candidate_hash,
		session_index,
		group_index,
		&validators,
	);

	gum::debug!(
		target: LOG_TARGET,
		para_id = %id,
		candidate_relay_parent = %candidate_relay_parent,
		?candidate_hash,
		pov_hash = ?pov.hash(),
		core = ?our_core,
		current_validators = ?validators,
		"Accepted collation, connecting to validators."
	);

	// Insert validator group for the `core_index` at relay parent.
	per_relay_parent.validator_group.entry(core_index).or_insert_with(|| {
		let mut group = ValidatorGroup::default();
		group.validators = validators;
		group
	});

	// Update a set of connected validators if necessary.
	connect_to_validators(ctx, cores_assigned, &state.validator_groups_buf).await;

	if let Some(result_sender) = result_sender {
		state.collation_result_senders.insert(candidate_hash, result_sender);
	}

	let para_head = receipt.descriptor.para_head();
	per_relay_parent.collations.insert(
		candidate_hash,
		CollationData {
			collation: Collation {
				receipt,
				pov,
				parent_head_data,
				status: CollationStatus::Created,
			},
			core_index,
			stats: per_relay_parent
				.block_number
				.map(|n| CollationStats::new(para_head, n, &state.metrics)),
		},
	);

	// The leaf should be present in the allowed ancestry of some leaf.
	//
	// It's collation-producer responsibility to verify that there exists
	// a hypothetical membership in a fragment chain for the candidate.
	let interested = state
		.peer_data
		.iter()
		.filter(|(_, PeerData { view: v, .. })| {
			v.iter().any(|block_hash| {
				state.implicit_view.as_ref().map(|implicit_view| {
					implicit_view
						.known_allowed_relay_parents_under(block_hash, Some(id))
						.unwrap_or_default()
						.contains(&candidate_relay_parent)
				}) == Some(true)
			})
		})
		.map(|(id, _)| id);

	// Make sure already connected peers get collations:
	for peer_id in interested {
		advertise_collation(
			ctx,
			candidate_relay_parent,
			per_relay_parent,
			peer_id,
			&state.peer_ids,
			&mut state.advertisement_timeouts,
			&state.metrics,
		)
		.await;
	}

	Ok(())
}

/// Validators of a particular group index.
#[derive(Debug)]
struct GroupValidators {
	/// The validators of above group (their discovery keys).
	validators: Vec<AuthorityDiscoveryId>,

	session_index: SessionIndex,
	group_index: GroupIndex,
}

/// Figure out current group of validators assigned to the para being collated on.
///
/// Returns [`ValidatorId`]'s of current group as determined based on the `relay_parent`.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn determine_our_validators<Context>(
	ctx: &mut Context,
	runtime: &mut RuntimeInfo,
	core_index: CoreIndex,
	relay_parent: Hash,
) -> Result<GroupValidators> {
	let session_index = runtime.get_session_index_for_child(ctx.sender(), relay_parent).await?;
	let info = &runtime
		.get_session_info_by_index(ctx.sender(), relay_parent, session_index)
		.await?
		.session_info;
	gum::debug!(target: LOG_TARGET, ?session_index, "Received session info");
	let groups = &info.validator_groups;
	let num_cores = groups.len();
	let rotation_info = get_group_rotation_info(ctx.sender(), relay_parent).await?;

	let current_group_index = rotation_info.group_for_core(core_index, num_cores);
	let current_validators =
		groups.get(current_group_index).map(|v| v.as_slice()).unwrap_or_default();

	let validators = &info.discovery_keys;

	let current_validators =
		current_validators.iter().map(|i| validators[i.0 as usize].clone()).collect();

	let current_validators = GroupValidators {
		validators: current_validators,
		session_index,
		group_index: current_group_index,
	};

	Ok(current_validators)
}

/// Construct the declare message to be sent to validator.
fn declare_message(
	state: &mut State,
) -> Option<CollationProtocols<protocol_v1::CollationProtocol, protocol_v2::CollationProtocol>> {
	let para_id = state.collating_on?;
	let declare_signature_payload = protocol_v2::declare_signature_payload(&state.local_peer_id);
	let wire_message = protocol_v2::CollatorProtocolMessage::Declare(
		state.collator_pair.public(),
		para_id,
		state.collator_pair.sign(&declare_signature_payload),
	);
	Some(CollationProtocols::V2(protocol_v2::CollationProtocol::CollatorProtocol(wire_message)))
}

/// Issue versioned `Declare` collation message to the given `peer`.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn declare<Context>(ctx: &mut Context, state: &mut State, peer: &PeerId) {
	if let Some(wire_message) = declare_message(state) {
		ctx.send_message(NetworkBridgeTxMessage::SendCollationMessage(vec![*peer], wire_message))
			.await;
	}
}

/// Checks whether there are any core assignments for our para on any active relay chain leaves.
fn has_assigned_cores(
	implicit_view: &Option<ImplicitView>,
	per_relay_parent: &HashMap<Hash, PerRelayParent>,
) -> bool {
	let Some(implicit_view) = implicit_view else { return false };

	for leaf in implicit_view.leaves() {
		if let Some(relay_parent) = per_relay_parent.get(leaf) {
			if !relay_parent.assignments.is_empty() {
				return true;
			}
		}
	}

	false
}

/// Updates a set of connected validators based on their advertisement-bits
/// in a validators buffer.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn connect_to_validators<Context>(
	ctx: &mut Context,
	cores_assigned: bool,
	validator_groups_buf: &ValidatorGroupsBuffer,
) {
	// If no cores are assigned to the para, we still need to send a ConnectToValidators request to
	// the network bridge passing an empty list of validator ids. Otherwise, it will keep connecting
	// to the last requested validators until a new request is issued.
	let validator_ids =
		if cores_assigned { validator_groups_buf.validators_to_connect() } else { Vec::new() };

	gum::trace!(
		target: LOG_TARGET,
		?cores_assigned,
		"Sending connection request to validators: {:?}",
		validator_ids,
	);

	// ignore address resolution failure
	// will reissue a new request on new collation
	let (failed, _) = oneshot::channel();
	ctx.send_message(NetworkBridgeTxMessage::ConnectToValidators {
		validator_ids,
		peer_set: PeerSet::Collation,
		failed,
	})
	.await;
}

/// Advertise collation to the given `peer`.
///
/// This will only advertise a collation if there exists at least one for the given
/// `relay_parent` and the given `peer` is set as validator for our para at the given
/// `relay_parent`.
///
/// We also make sure not to advertise the same collation multiple times to the same validator.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn advertise_collation<Context>(
	ctx: &mut Context,
	relay_parent: Hash,
	per_relay_parent: &mut PerRelayParent,
	peer: &PeerId,
	peer_ids: &HashMap<PeerId, HashSet<AuthorityDiscoveryId>>,
	advertisement_timeouts: &mut FuturesUnordered<ResetInterestTimeout>,
	metrics: &Metrics,
) {
	for (candidate_hash, collation_and_core) in per_relay_parent.collations.iter_mut() {
		let core_index = *collation_and_core.core_index();
		let collation = collation_and_core.collation_mut();

		let Some(validator_group) = per_relay_parent.validator_group.get_mut(&core_index) else {
			gum::debug!(
				target: LOG_TARGET,
				?relay_parent,
				?core_index,
				"Skipping advertising to validator, validator group for core not found",
			);
			return
		};

		let should_advertise = validator_group.should_advertise_to(candidate_hash, peer_ids, &peer);
		match should_advertise {
			ShouldAdvertiseTo::Yes => {},
			ShouldAdvertiseTo::NotAuthority | ShouldAdvertiseTo::AlreadyAdvertised => {
				gum::trace!(
					target: LOG_TARGET,
					?relay_parent,
					?candidate_hash,
					peer_id = %peer,
					reason = ?should_advertise,
					"Not advertising collation"
				);
				continue
			},
		}

		gum::debug!(
			target: LOG_TARGET,
			?relay_parent,
			?candidate_hash,
			peer_id = %peer,
			"Advertising collation.",
		);

		collation.status.advance_to_advertised();

		ctx.send_message(NetworkBridgeTxMessage::SendCollationMessage(
			vec![*peer],
			CollationProtocols::V2(protocol_v2::CollationProtocol::CollatorProtocol(
				protocol_v2::CollatorProtocolMessage::AdvertiseCollation {
					relay_parent,
					candidate_hash: *candidate_hash,
					parent_head_data_hash: collation.parent_head_data.hash(),
				},
			)),
		))
		.await;

		validator_group.advertised_to_peer(candidate_hash, &peer_ids, peer);

		advertisement_timeouts.push(ResetInterestTimeout::new(
			*candidate_hash,
			*peer,
			RESET_INTEREST_TIMEOUT,
		));

		metrics.on_advertisement_made();
	}
}

/// The main incoming message dispatching switch.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn process_msg<Context>(
	ctx: &mut Context,
	runtime: &mut RuntimeInfo,
	state: &mut State,
	msg: CollatorProtocolMessage,
) -> Result<()> {
	use CollatorProtocolMessage::*;

	match msg {
		CollateOn(id) => {
			state.collating_on = Some(id);
			state.implicit_view = Some(ImplicitView::new(Some(id)));
		},
		DistributeCollation {
			candidate_receipt,
			parent_head_data_hash: _,
			pov,
			parent_head_data,
			result_sender,
			core_index,
		} => {
			match state.collating_on {
				Some(id) if candidate_receipt.descriptor.para_id() != id => {
					// If the ParaId of a collation requested to be distributed does not match
					// the one we expect, we ignore the message.
					gum::warn!(
						target: LOG_TARGET,
						para_id = %candidate_receipt.descriptor.para_id(),
						collating_on = %id,
						"DistributeCollation for unexpected para_id",
					);
				},
				Some(id) => {
					let _ = state.metrics.time_collation_distribution("distribute");
					distribute_collation(
						ctx,
						runtime,
						state,
						id,
						candidate_receipt,
						pov,
						parent_head_data,
						result_sender,
						core_index,
					)
					.await?;
				},
				None => {
					gum::warn!(
						target: LOG_TARGET,
						para_id = %candidate_receipt.descriptor.para_id(),
						"DistributeCollation message while not collating on any",
					);
				},
			}
		},
		NetworkBridgeUpdate(event) => {
			// We should count only this shoulder in the histogram, as other shoulders are just
			// introducing noise
			let _ = state.metrics.time_process_msg();

			if let Err(e) = handle_network_msg(ctx, runtime, state, event).await {
				gum::warn!(
					target: LOG_TARGET,
					err = ?e,
					"Failed to handle incoming network message",
				);
			}
		},
		msg @ (Invalid(..) | Seconded(..)) => {
			gum::warn!(
				target: LOG_TARGET,
				"{:?} message is not expected on the collator side of the protocol",
				msg,
			);
		},
	}

	Ok(())
}

/// Issue a response to a previously requested collation.
async fn send_collation(
	state: &mut State,
	request: VersionedCollationRequest,
	receipt: CandidateReceipt,
	pov: PoV,
	parent_head_data: HeadData,
) {
	let (tx, rx) = oneshot::channel();

	let relay_parent = request.relay_parent();
	let peer_id = request.peer_id();
	let candidate_hash = receipt.hash();

	let result = Ok(request_v2::CollationFetchingResponse::CollationWithParentHeadData {
		receipt,
		pov,
		parent_head_data,
	});

	let response =
		OutgoingResponse { result, reputation_changes: Vec::new(), sent_feedback: Some(tx) };

	if let Err(_) = request.send_outgoing_response(response) {
		gum::warn!(target: LOG_TARGET, "Sending collation response failed");
	}

	state.active_collation_fetches.push(
		async move {
			let r = rx.timeout(MAX_UNSHARED_UPLOAD_TIME).await;
			let timed_out = r.is_none();

			CollationSendResult { relay_parent, candidate_hash, peer_id, timed_out }
		}
		.boxed(),
	);

	state.metrics.on_collation_sent();
}

/// A networking messages switch.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn handle_incoming_peer_message<Context>(
	ctx: &mut Context,
	runtime: &mut RuntimeInfo,
	state: &mut State,
	origin: PeerId,
	msg: CollationProtocols<
		protocol_v1::CollatorProtocolMessage,
		protocol_v2::CollatorProtocolMessage,
	>,
) -> Result<()> {
	use protocol_v1::CollatorProtocolMessage as V1;
	use protocol_v2::CollatorProtocolMessage as V2;

	match msg {
		CollationProtocols::V1(V1::Declare(..)) | CollationProtocols::V2(V2::Declare(..)) => {
			gum::trace!(
				target: LOG_TARGET,
				?origin,
				"Declare message is not expected on the collator side of the protocol",
			);

			// If we are declared to, this is another collator, and we should disconnect.
			ctx.send_message(NetworkBridgeTxMessage::DisconnectPeers(
				vec![origin],
				PeerSet::Collation,
			))
			.await;
		},
		CollationProtocols::V1(V1::AdvertiseCollation(_)) |
		CollationProtocols::V2(V2::AdvertiseCollation { .. }) => {
			gum::trace!(
				target: LOG_TARGET,
				?origin,
				"AdvertiseCollation message is not expected on the collator side of the protocol",
			);

			modify_reputation(&mut state.reputation, ctx.sender(), origin, COST_UNEXPECTED_MESSAGE)
				.await;

			// If we are advertised to, this is another collator, and we should disconnect.
			ctx.send_message(NetworkBridgeTxMessage::DisconnectPeers(
				vec![origin],
				PeerSet::Collation,
			))
			.await;
		},
		CollationProtocols::V1(V1::CollationSeconded(relay_parent, statement)) => {
			// Impossible, we no longer accept connections on v1.
			gum::warn!(
				target: LOG_TARGET,
				?statement,
				?origin,
				?relay_parent,
				"Collation seconded message received on unsupported protocol version 1",
			);
		},
		CollationProtocols::V2(V2::CollationSeconded(relay_parent, statement)) => {
			if !matches!(statement.unchecked_payload(), Statement::Seconded(_)) {
				gum::warn!(
					target: LOG_TARGET,
					?statement,
					?origin,
					"Collation seconded message received with none-seconded statement.",
				);
			} else {
				let statement = runtime
					.check_signature(ctx.sender(), relay_parent, statement)
					.await?
					.map_err(Error::InvalidStatementSignature)?;

				let removed =
					state.collation_result_senders.remove(&statement.payload().candidate_hash());

				if let Some(sender) = removed {
					gum::trace!(
						target: LOG_TARGET,
						?statement,
						?origin,
						"received a valid `CollationSeconded`, forwarding result to collator",
					);
					let _ = sender.send(CollationSecondedSignal { statement, relay_parent });
				} else {
					// Checking whether the `CollationSeconded` statement is unexpected
					let relay_parent = match state.per_relay_parent.get(&relay_parent) {
						Some(per_relay_parent) => per_relay_parent,
						None => {
							gum::debug!(
								target: LOG_TARGET,
								candidate_relay_parent = %relay_parent,
								candidate_hash = ?&statement.payload().candidate_hash(),
								"Seconded statement relay parent is out of our view",
							);
							return Ok(())
						},
					};
					match relay_parent.collations.get(&statement.payload().candidate_hash()) {
						Some(_) => {
							// We've seen this collation before, so a seconded statement is expected
							gum::trace!(
								target: LOG_TARGET,
								?statement,
								?origin,
								"received a valid `CollationSeconded`",
							);
						},
						None => {
							gum::debug!(
								target: LOG_TARGET,
								candidate_hash = ?&statement.payload().candidate_hash(),
								?origin,
								"received an unexpected `CollationSeconded`: unknown statement",
							);
						},
					}
				}
			}
		},
	}

	Ok(())
}

/// Process an incoming network request for a collation.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn handle_incoming_request<Context>(
	ctx: &mut Context,
	state: &mut State,
	req: std::result::Result<VersionedCollationRequest, incoming::Error>,
) -> Result<()> {
	let req = req?;
	let relay_parent = req.relay_parent();
	let peer_id = req.peer_id();
	let para_id = req.para_id();

	match state.collating_on {
		Some(our_para_id) if our_para_id == para_id => {
			let per_relay_parent = match state.per_relay_parent.get_mut(&relay_parent) {
				Some(per_relay_parent) => per_relay_parent,
				None => {
					gum::debug!(
						target: LOG_TARGET,
						relay_parent = %relay_parent,
						"received a `RequestCollation` for a relay parent out of our view",
					);

					return Ok(())
				},
			};

			let collation_with_core = match &req {
				VersionedCollationRequest::V2(req) =>
					per_relay_parent.collations.get_mut(&req.payload.candidate_hash),
			};
			let (receipt, pov, parent_head_data) =
				if let Some(collation_with_core) = collation_with_core {
					let collation = collation_with_core.collation_mut();
					collation.status.advance_to_requested();
					(
						collation.receipt.clone(),
						collation.pov.clone(),
						collation.parent_head_data.clone(),
					)
				} else {
					gum::warn!(
						target: LOG_TARGET,
						relay_parent = %relay_parent,
						"received a `RequestCollation` for a relay parent we don't have collation stored.",
					);

					return Ok(())
				};

			state.metrics.on_collation_sent_requested();

			let waiting = state.waiting_collation_fetches.entry(relay_parent).or_default();
			let candidate_hash = receipt.hash();

			if !waiting.waiting_peers.insert((peer_id, candidate_hash)) {
				gum::debug!(
					target: LOG_TARGET,
					"Dropping incoming request as peer has a request in flight already."
				);
				modify_reputation(
					&mut state.reputation,
					ctx.sender(),
					peer_id,
					COST_APPARENT_FLOOD.into(),
				)
				.await;
				return Ok(())
			}

			if waiting.collation_fetch_active {
				waiting.req_queue.push_back(req);
			} else {
				waiting.collation_fetch_active = true;
				// Obtain a timer for sending collation
				let _ = state.metrics.time_collation_distribution("send");

				send_collation(state, req, receipt, pov, parent_head_data).await;
			}
		},
		Some(our_para_id) => {
			gum::warn!(
				target: LOG_TARGET,
				for_para_id = %para_id,
				our_para_id = %our_para_id,
				"received a `CollationFetchingRequest` for unexpected para_id",
			);
		},
		None => {
			gum::warn!(
				target: LOG_TARGET,
				for_para_id = %para_id,
				"received a `RequestCollation` while not collating on any para",
			);
		},
	}
	Ok(())
}

/// Peer's view has changed. Send advertisements for new relay parents
/// if there're any.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn handle_peer_view_change<Context>(
	ctx: &mut Context,
	state: &mut State,
	peer_id: PeerId,
	view: View,
) {
	let Some(PeerData { view: current, unknown_heads }) = state.peer_data.get_mut(&peer_id) else {
		return
	};

	let added: Vec<Hash> = view.difference(&*current).cloned().collect();

	*current = view;

	for added in added.into_iter() {
		let block_hashes = match state.per_relay_parent.contains_key(&added) {
			true => state
				.implicit_view
				.as_ref()
				.and_then(|implicit_view| {
					implicit_view.known_allowed_relay_parents_under(&added, state.collating_on)
				})
				.unwrap_or_default(),
			false => {
				gum::trace!(
					target: LOG_TARGET,
					?peer_id,
					new_leaf = ?added,
					"New leaf in peer's view is unknown",
				);

				unknown_heads.insert(added, ());

				continue
			},
		};

		for block_hash in block_hashes {
			let Some(per_relay_parent) = state.per_relay_parent.get_mut(block_hash) else {
				continue
			};

			advertise_collation(
				ctx,
				*block_hash,
				per_relay_parent,
				&peer_id,
				&state.peer_ids,
				&mut state.advertisement_timeouts,
				&state.metrics,
			)
			.await;
		}
	}
}

/// Bridge messages switch.
#[overseer::contextbounds(CollatorProtocol, prefix = self::overseer)]
async fn handle_network_msg<Context>(
	ctx: &mut Context,
	runtime: &mut RuntimeInfo,
	state: &mut State,
	bridge_message: NetworkBridgeEvent<net_protocol::CollatorProtocolMessage>,
) -> Result<()> {
	use NetworkBridgeEvent::*;

	match bridge_message {
		PeerConnected(peer_id, observed_role, protocol_version, maybe_authority) => {
			// If it is possible that a disconnected validator would attempt a reconnect
			// it should be handled here.
			gum::trace!(target: LOG_TARGET, ?peer_id, ?observed_role, ?maybe_authority, "Peer connected");

			let version: CollationVersion = match protocol_version.try_into() {
				Ok(version) => version,
				Err(err) => {
					// Network bridge is expected to handle this.
					gum::error!(
						target: LOG_TARGET,
						?peer_id,
						?observed_role,
						?err,
						"Unsupported protocol version"
					);
					return Ok(())
				},
			};
			if version == CollationVersion::V1 {
				gum::warn!(
					target: LOG_TARGET,
					?peer_id,
					?observed_role,
					"Unsupported protocol version v1"
				);

				// V1 no longer supported, we should disconnect.
				ctx.send_message(NetworkBridgeTxMessage::DisconnectPeers(
					vec![peer_id],
					PeerSet::Collation,
				))
				.await;
				return Ok(())
			}

			state.peer_data.entry(peer_id).or_insert_with(|| PeerData {
				view: View::default(),
				// Unlikely that the collator is falling 10 blocks behind and if so, it probably is
				// not able to keep up any way.
				unknown_heads: LruMap::new(ByLength::new(10)),
			});

			if let Some(authority_ids) = maybe_authority {
				gum::trace!(
					target: LOG_TARGET,
					?authority_ids,
					?peer_id,
					"Connected to requested validator"
				);
				state.peer_ids.insert(peer_id, authority_ids);

				declare(ctx, state, &peer_id).await;
			}
		},
		PeerViewChange(peer_id, view) => {
			gum::trace!(target: LOG_TARGET, ?peer_id, ?view, "Peer view change");
			handle_peer_view_change(ctx, state, peer_id, view).await;
		},
		PeerDisconnected(peer_id) => {
			gum::trace!(target: LOG_TARGET, ?peer_id, "Peer disconnected");
			state.peer_data.remove(&peer_id);
			state.peer_ids.remove(&peer_id);
		},
		OurViewChange(view) => {
			gum::trace!(target: LOG_TARGET, ?view, "Own view change");
			handle_our_view_change(ctx, state, view).await?;
		},
		PeerMessage(remote, msg) => {
			handle_incoming_peer_message(ctx, runtime, state, remote, msg).await?;
		},
		UpdatedAuthorityIds(peer_id, authority_ids) => {
			gum::trace!(target: LOG_TARGET, ?peer_id, ?authority_ids, "Updated authority ids");
			if state.peer_data.contains_key(&peer_id) {
				if state.peer_ids.insert(peer_id, authority_ids).is_none() {
					declare(ctx, state, &peer_id).await;
				}
			}
		},
		NewGossipTopology { .. } => {
			// impossible!
		},
	}

	Ok(())
}

/// Update collation tracker with the backed and included candidates.
#[overseer::contextbounds(CollatorProtocol, prefix = crate::overseer)]
async fn process_block_events<Context>(
	ctx: &mut Context,
	collation_tracker: &mut CollationTracker,
	leaf: Hash,
	maybe_block_number: Option<BlockNumber>,
	para_id: ParaId,
	metrics: &Metrics,
) {
	if let Ok(events) = get_candidate_events(ctx.sender(), leaf).await {
		let Some(block_number) = maybe_block_number else {
			// This should not happen. If it does this log message explains why
			// metrics and logs are missing for the candidates under this block.
			gum::debug!(
				target: crate::LOG_TARGET_STATS,
				relay_block = ?leaf,
				?para_id,
				"Failed to get relay chain block number",
			);
			return
		};

		for ev in events {
			match ev {
				CandidateEvent::CandidateIncluded(receipt, _, _, _) => {
					if receipt.descriptor.para_id() != para_id {
						continue
					}
					collation_tracker.collation_included(block_number, leaf, receipt, metrics);
				},
				CandidateEvent::CandidateBacked(receipt, _, _, _) => {
					if receipt.descriptor.para_id() != para_id {
						continue
					}

					let Some(block_number) = maybe_block_number else { continue };
					let Some(stats) =
						collation_tracker.collation_backed(block_number, leaf, receipt, metrics)
					else {
						continue
					};

					// Continue measuring inclusion latency.
					collation_tracker.track(stats);
				},
				_ => {
					// do not care about other events
				},
			}
		}
	}
}

/// Handles our view changes.
#[overseer::contextbounds(CollatorProtocol, prefix = crate::overseer)]
async fn handle_our_view_change<Context>(
	ctx: &mut Context,
	state: &mut State,
	view: OurView,
) -> Result<()> {
	let Some(implicit_view) = &mut state.implicit_view else { return Ok(()) };
	let Some(para_id) = state.collating_on else { return Ok(()) };

	let removed: Vec<_> =
		implicit_view.leaves().map(|l| *l).filter(|h| !view.contains(h)).collect();
	let added: Vec<_> = view.iter().filter(|h| !implicit_view.contains_leaf(h)).collect();

	for leaf in added {
		let claim_queue: ClaimQueueSnapshot = fetch_claim_queue(ctx.sender(), *leaf).await?;

		implicit_view
			.activate_leaf(ctx.sender(), *leaf)
			.await
			.map_err(Error::ImplicitViewFetchError)?;

		let block_number = implicit_view.block_number(leaf);
		state
			.per_relay_parent
			.insert(*leaf, PerRelayParent::new(para_id, claim_queue, block_number));

		process_block_events(
			ctx,
			&mut state.collation_tracker,
			*leaf,
			block_number,
			para_id,
			&state.metrics,
		)
		.await;
		let allowed_ancestry = implicit_view
			.known_allowed_relay_parents_under(leaf, state.collating_on)
			.unwrap_or_default();

		// Get the peers that already reported us this head, but we didn't know it at this
		// point.
		let peers = state
			.peer_data
			.iter_mut()
			.filter_map(|(id, data)| data.unknown_heads.remove(leaf).map(|_| id))
			.collect::<Vec<_>>();

		for block_hash in allowed_ancestry {
			let block_number = implicit_view.block_number(block_hash);

			if state.per_relay_parent.get(block_hash).is_none() {
				let claim_queue = fetch_claim_queue(ctx.sender(), *block_hash).await?;
				state
					.per_relay_parent
					.insert(*block_hash, PerRelayParent::new(para_id, claim_queue, block_number));
			}

			let per_relay_parent =
				state.per_relay_parent.get_mut(block_hash).expect("Just inserted");

			// Announce relevant collations to these peers.
			for peer_id in &peers {
				advertise_collation(
					ctx,
					*block_hash,
					per_relay_parent,
					&peer_id,
					&state.peer_ids,
					&mut state.advertisement_timeouts,
					&state.metrics,
				)
				.await;
			}
		}
	}

	for leaf in removed {
		// If the leaf is deactivated it still may stay in the view as a part
		// of implicit ancestry. Only update the state after the hash is actually
		// pruned from the block info storage.
		let maybe_block_number = implicit_view.block_number(&leaf);
		let pruned = implicit_view.deactivate_leaf(leaf);

		for removed in &pruned {
			gum::debug!(target: LOG_TARGET, relay_parent = ?removed, "Removing relay parent because our view changed.");

			if let Some(block_number) = maybe_block_number {
				let expired_collations = state.collation_tracker.drain_expired(block_number);
				process_expired_collations(expired_collations, *removed, para_id, &state.metrics);
			}

			// Get all the collations built on top of the removed feaf.
			let collations = state
				.per_relay_parent
				.remove(removed)
				.map(|per_relay_parent| per_relay_parent.collations)
				.unwrap_or_default();

			for collation_with_core in collations.into_values() {
				let collation = collation_with_core.collation();
				let candidate_hash: CandidateHash = collation.receipt.hash();

				state.collation_result_senders.remove(&candidate_hash);
				state.validator_groups_buf.remove_candidate(&candidate_hash);

				process_out_of_view_collation(&mut state.collation_tracker, collation_with_core);
			}

			state.waiting_collation_fetches.remove(removed);
		}
	}
	Ok(())
}

fn process_out_of_view_collation(
	collation_tracker: &mut CollationTracker,
	mut collation_with_core: CollationData,
) {
	let collation = collation_with_core.collation();
	let candidate_hash: CandidateHash = collation.receipt.hash();

	match collation.status {
		CollationStatus::Created => gum::warn!(
			target: LOG_TARGET,
			?candidate_hash,
			pov_hash = ?collation.pov.hash(),
			"Collation wasn't advertised to any validator.",
		),
		CollationStatus::Advertised => gum::debug!(
			target: LOG_TARGET,
			?candidate_hash,
			pov_hash = ?collation.pov.hash(),
			"Collation was advertised but not requested by any validator.",
		),
		CollationStatus::Requested => {
			gum::debug!(
				target: LOG_TARGET,
				?candidate_hash,
				pov_hash = ?collation.pov.hash(),
				"Collation was requested.",
			);
		},
	}

	let collation_status = collation.status.clone();
	let Some(mut stats) = collation_with_core.take_stats() else { return };

	// If the collation stats are still available, it means it was never
	// succesfully fetched, even if a fetch request was received, but not succeed.
	//
	// Will expire in it's current state at the next block import.
	stats.set_pre_backing_status(collation_status);
	collation_tracker.track(stats);
}

fn process_expired_collations(
	expired_collations: Vec<CollationStats>,
	removed: Hash,
	para_id: ParaId,
	metrics: &Metrics,
) {
	for expired_collation in expired_collations {
		let collation_state = if expired_collation.fetch_latency().is_none() {
			// If collation was not fetched, we rely on the status provided
			// by the collator protocol.
			expired_collation.pre_backing_status().label()
		} else if expired_collation.backed().is_none() {
			"fetched"
		} else if expired_collation.included().is_none() {
			"backed"
		} else {
			"none"
		};

		let age = expired_collation.expired().unwrap_or_default();
		gum::debug!(
			target: crate::LOG_TARGET_STATS,
			?age,
			?collation_state,
			relay_parent = ?removed,
			?para_id,
			head = ?expired_collation.head(),
			"Collation expired",
		);

		metrics.on_collation_expired(age as f64, collation_state);
	}
}

/// The collator protocol collator side main loop.
#[overseer::contextbounds(CollatorProtocol, prefix = crate::overseer)]
pub(crate) async fn run<Context>(
	ctx: Context,
	local_peer_id: PeerId,
	collator_pair: CollatorPair,
	req_v2_receiver: IncomingRequestReceiver<request_v2::CollationFetchingRequest>,
	metrics: Metrics,
) -> std::result::Result<(), FatalError> {
	run_inner(
		ctx,
		local_peer_id,
		collator_pair,
		req_v2_receiver,
		metrics,
		ReputationAggregator::default(),
		REPUTATION_CHANGE_INTERVAL,
	)
	.await
}

#[overseer::contextbounds(CollatorProtocol, prefix = crate::overseer)]
async fn run_inner<Context>(
	mut ctx: Context,
	local_peer_id: PeerId,
	collator_pair: CollatorPair,
	mut req_v2_receiver: IncomingRequestReceiver<request_v2::CollationFetchingRequest>,
	metrics: Metrics,
	reputation: ReputationAggregator,
	reputation_interval: Duration,
) -> std::result::Result<(), FatalError> {
	use OverseerSignal::*;

	let new_reputation_delay = || futures_timer::Delay::new(reputation_interval).fuse();
	let mut reputation_delay = new_reputation_delay();

	let mut state = State::new(local_peer_id, collator_pair, metrics.clone(), reputation);
	let mut runtime = RuntimeInfo::new(None);

	loop {
		let reputation_changes = || vec![COST_INVALID_REQUEST];
		let recv_req_v2 = req_v2_receiver.recv(reputation_changes).fuse();
		pin_mut!(recv_req_v2);

		let mut reconnect_timeout = &mut state.reconnect_timeout;
		select! {
			_ = reputation_delay => {
				state.reputation.send(ctx.sender()).await;
				reputation_delay = new_reputation_delay();
			},
			msg = ctx.recv().fuse() => match msg.map_err(FatalError::SubsystemReceive)? {
				FromOrchestra::Communication { msg } => {
					log_error(
						process_msg(&mut ctx, &mut runtime, &mut state, msg).await,
						"Failed to process message"
					)?;
				},
				FromOrchestra::Signal(ActiveLeaves(update)) => {
					if update.activated.is_some() {
						*reconnect_timeout = futures_timer::Delay::new(RECONNECT_AFTER_LEAF_TIMEOUT).fuse();
					}
				}
				FromOrchestra::Signal(BlockFinalized(..)) => {}
				FromOrchestra::Signal(Conclude) => return Ok(()),
			},
			CollationSendResult { relay_parent, candidate_hash, peer_id, timed_out } =
				state.active_collation_fetches.select_next_some() => {

				let next = if let Some(waiting) = state.waiting_collation_fetches.get_mut(&relay_parent) {
					if timed_out {
						gum::debug!(
							target: LOG_TARGET_STATS,
							?relay_parent,
							?peer_id,
							?candidate_hash,
							"Sending collation to validator timed out, carrying on with next validator."
						);
						// We try to throttle requests per relay parent to give validators
						// more bandwidth, but if the collation is not received within the
						// timeout, we simply start processing next request.
						// The request it still alive, it should be kept in a waiting queue.
					} else {
						for authority_id in state.peer_ids.get(&peer_id).into_iter().flatten() {
							// This peer has received the candidate. Not interested anymore.
							state.validator_groups_buf.reset_validator_interest(candidate_hash, authority_id);
						}
						waiting.waiting_peers.remove(&(peer_id, candidate_hash));

						// Update collation status to fetched.
						if let Some(per_relay_parent) =  state.per_relay_parent.get_mut(&relay_parent) {
							if let Some(collation_with_core) = per_relay_parent.collations.get_mut(&candidate_hash) {
								let maybe_stats = collation_with_core.take_stats();
								let our_para_id = collation_with_core.collation().receipt.descriptor.para_id();

								if let Some(mut stats) = maybe_stats {
									// Update the timestamp when collation has been sent (from subsysytem perspective)
									stats.set_fetched_at(std::time::Instant::now());
									gum::debug!(
										target: LOG_TARGET_STATS,
										para_head = ?stats.head(),
										%our_para_id,
										"Collation fetch latency is {}ms",
										stats.fetch_latency().unwrap_or_default().as_millis(),
									);

									// Update the pre-backing status. Should be requested at this point.
									stats.set_pre_backing_status(collation_with_core.collation().status.clone());
									debug_assert_eq!(collation_with_core.collation().status, CollationStatus::Requested);

									// Observe fetch latency metric.
									stats.take_fetch_latency_metric();
									stats.set_backed_latency_metric(metrics.time_collation_backing_latency());

									// Next step is to measure backing latency.
									state.collation_tracker.track(stats);
								}
							}
						}
					}

					if let Some(next) = waiting.req_queue.pop_front() {
						next
					} else {
						waiting.collation_fetch_active = false;
						continue
					}
				} else {
					// No waiting collation fetches means we already removed the relay parent from our view.
					continue
				};

				let next_collation_with_core = {
					let per_relay_parent = match state.per_relay_parent.get(&relay_parent) {
						Some(per_relay_parent) => per_relay_parent,
						None => continue,
					};

					per_relay_parent.collations.get(&next.candidate_hash())
				};

				if let Some(collation_with_core) = next_collation_with_core {
					let collation = collation_with_core.collation();
					let receipt = collation.receipt.clone();
					let pov = collation.pov.clone();
					let parent_head_data = collation.parent_head_data.clone();

					send_collation(&mut state, next, receipt, pov, parent_head_data).await;
				}
			},
			(candidate_hash, peer_id) = state.advertisement_timeouts.select_next_some() => {
				// NOTE: it doesn't necessarily mean that a validator gets disconnected,
				// it only will if there're no other advertisements we want to send.
				//
				// No-op if the collation was already fetched or went out of view.
				for authority_id in state.peer_ids.get(&peer_id).into_iter().flatten() {
					state
						.validator_groups_buf
						.reset_validator_interest(candidate_hash, &authority_id);
				}
			}
			_ = reconnect_timeout => {
				let cores_assigned = has_assigned_cores(&state.implicit_view, &state.per_relay_parent);
				connect_to_validators(&mut ctx, cores_assigned, &state.validator_groups_buf).await;

				gum::trace!(
					target: LOG_TARGET,
					timeout = ?RECONNECT_AFTER_LEAF_TIMEOUT,
					"Peer-set updated due to a timeout"
				);
			},
			in_req = recv_req_v2 => {
				let request = in_req.map(VersionedCollationRequest::from);

				log_error(
					handle_incoming_request(&mut ctx, &mut state, request).await,
					"Handling incoming collation fetch request V2"
				)?;
			}
		}
	}
}
