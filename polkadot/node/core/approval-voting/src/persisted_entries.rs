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

//! Entries pertaining to approval which need to be persisted.
//!
//! The actual persisting of data is handled by the `approval_db` module.
//! Within that context, things are plain-old-data. Within this module,
//! data and logic are intertwined.

use itertools::Itertools;
use polkadot_node_primitives::approval::{
	v1::{DelayTranche, RelayVRFStory},
	v2::{AssignmentCertV2, CandidateBitfield},
};
use polkadot_primitives::{
	vstaging::CandidateReceiptV2 as CandidateReceipt, BlockNumber, CandidateHash, CandidateIndex,
	CoreIndex, GroupIndex, Hash, SessionIndex, ValidatorIndex, ValidatorSignature,
};
use sp_consensus_slots::Slot;

use bitvec::{order::Lsb0 as BitOrderLsb0, slice::BitSlice};
use std::collections::BTreeMap;

use crate::approval_db::v2::Bitfield;

use super::criteria::OurAssignment;

use polkadot_node_primitives::approval::time::Tick;

/// Metadata regarding a specific tranche of assignments for a specific candidate.
#[derive(Debug, Clone, PartialEq)]
pub struct TrancheEntry {
	tranche: DelayTranche,
	// Assigned validators, and the instant we received their assignment, rounded
	// to the nearest tick.
	assignments: Vec<(ValidatorIndex, Tick)>,
}

impl TrancheEntry {
	/// Get the tranche of this entry.
	pub fn tranche(&self) -> DelayTranche {
		self.tranche
	}

	/// Get the assignments for this entry.
	pub fn assignments(&self) -> &[(ValidatorIndex, Tick)] {
		&self.assignments
	}
}

impl From<crate::approval_db::v2::TrancheEntry> for TrancheEntry {
	fn from(entry: crate::approval_db::v2::TrancheEntry) -> Self {
		TrancheEntry {
			tranche: entry.tranche,
			assignments: entry.assignments.into_iter().map(|(v, t)| (v, t.into())).collect(),
		}
	}
}

impl From<TrancheEntry> for crate::approval_db::v2::TrancheEntry {
	fn from(entry: TrancheEntry) -> Self {
		Self {
			tranche: entry.tranche,
			assignments: entry.assignments.into_iter().map(|(v, t)| (v, t.into())).collect(),
		}
	}
}

impl From<crate::approval_db::v3::OurApproval> for OurApproval {
	fn from(approval: crate::approval_db::v3::OurApproval) -> Self {
		Self {
			signature: approval.signature,
			signed_candidates_indices: approval.signed_candidates_indices,
		}
	}
}
impl From<OurApproval> for crate::approval_db::v3::OurApproval {
	fn from(approval: OurApproval) -> Self {
		Self {
			signature: approval.signature,
			signed_candidates_indices: approval.signed_candidates_indices,
		}
	}
}

/// Metadata about our approval signature
#[derive(Debug, Clone, PartialEq)]
pub struct OurApproval {
	/// The signature for the candidates hashes pointed by indices.
	pub signature: ValidatorSignature,
	/// The indices of the candidates signed in this approval.
	pub signed_candidates_indices: CandidateBitfield,
}

impl OurApproval {
	/// Converts a ValidatorSignature to an OurApproval.
	/// It used in converting the database from v1 to latest.
	pub fn from_v1(value: ValidatorSignature, candidate_index: CandidateIndex) -> Self {
		Self { signature: value, signed_candidates_indices: candidate_index.into() }
	}

	/// Converts a ValidatorSignature to an OurApproval.
	/// It used in converting the database from v2 to latest.
	pub fn from_v2(value: ValidatorSignature, candidate_index: CandidateIndex) -> Self {
		Self::from_v1(value, candidate_index)
	}
}
/// Metadata regarding approval of a particular candidate within the context of some
/// particular block.
#[derive(Debug, Clone, PartialEq)]
pub struct ApprovalEntry {
	tranches: Vec<TrancheEntry>,
	backing_group: GroupIndex,
	our_assignment: Option<OurAssignment>,
	our_approval_sig: Option<OurApproval>,
	// `n_validators` bits.
	assigned_validators: Bitfield,
	approved: bool,
}

impl ApprovalEntry {
	/// Convenience constructor
	pub fn new(
		tranches: Vec<TrancheEntry>,
		backing_group: GroupIndex,
		our_assignment: Option<OurAssignment>,
		our_approval_sig: Option<OurApproval>,
		// `n_validators` bits.
		assigned_validators: Bitfield,
		approved: bool,
	) -> Self {
		Self {
			tranches,
			backing_group,
			our_assignment,
			our_approval_sig,
			assigned_validators,
			approved,
		}
	}

	// Access our assignment for this approval entry.
	pub fn our_assignment(&self) -> Option<&OurAssignment> {
		self.our_assignment.as_ref()
	}

	// Note that our assignment is triggered. No-op if already triggered.
	pub fn trigger_our_assignment(
		&mut self,
		tick_now: Tick,
	) -> Option<(AssignmentCertV2, ValidatorIndex, DelayTranche)> {
		let our = self.our_assignment.as_mut().and_then(|a| {
			if a.triggered() {
				return None
			}
			a.mark_triggered();

			Some(a.clone())
		});

		our.map(|a| {
			self.import_assignment(a.tranche(), a.validator_index(), tick_now, false);

			(a.cert().clone(), a.validator_index(), a.tranche())
		})
	}

	/// Import our local approval vote signature for this candidate.
	pub fn import_approval_sig(&mut self, approval_sig: OurApproval) {
		self.our_approval_sig = Some(approval_sig);
	}

	/// Whether a validator is already assigned.
	pub fn is_assigned(&self, validator_index: ValidatorIndex) -> bool {
		self.assigned_validators
			.get(validator_index.0 as usize)
			.map(|b| *b)
			.unwrap_or(false)
	}

	/// Import an assignment. No-op if already assigned on the same tranche.
	pub fn import_assignment(
		&mut self,
		tranche: DelayTranche,
		validator_index: ValidatorIndex,
		tick_now: Tick,
		is_duplicate: bool,
	) {
		// linear search probably faster than binary. not many tranches typically.
		let idx = match self.tranches.iter().position(|t| t.tranche >= tranche) {
			Some(pos) => {
				if self.tranches[pos].tranche > tranche {
					self.tranches.insert(pos, TrancheEntry { tranche, assignments: Vec::new() });
				}

				pos
			},
			None => {
				self.tranches.push(TrancheEntry { tranche, assignments: Vec::new() });

				self.tranches.len() - 1
			},
		};
		// At restart we might have duplicate assignments because approval-distribution is not
		// persistent across restarts, so avoid adding duplicates.
		// We already know if we have seen an assignment from this validator and since this
		// function is on the hot path we can avoid iterating through tranches by using
		// !is_duplicate to determine if it is already present in the vector and does not need
		// adding.
		if !is_duplicate {
			self.tranches[idx].assignments.push((validator_index, tick_now));
		}
		self.assigned_validators.set(validator_index.0 as _, true);
	}

	// Produce a bitvec indicating the assignments of all validators up to and
	// including `tranche`.
	pub fn assignments_up_to(&self, tranche: DelayTranche) -> Bitfield {
		self.tranches.iter().take_while(|e| e.tranche <= tranche).fold(
			bitvec::bitvec![u8, BitOrderLsb0; 0; self.assigned_validators.len()],
			|mut a, e| {
				for &(v, _) in &e.assignments {
					a.set(v.0 as _, true);
				}

				a
			},
		)
	}

	/// Whether the approval entry is approved
	pub fn is_approved(&self) -> bool {
		self.approved
	}

	/// Mark the approval entry as approved.
	pub fn mark_approved(&mut self) {
		self.approved = true;
	}

	/// Access the tranches.
	pub fn tranches(&self) -> &[TrancheEntry] {
		&self.tranches
	}

	/// Get the number of validators in this approval entry.
	pub fn n_validators(&self) -> usize {
		self.assigned_validators.len()
	}

	/// Get the number of assignments by validators, including the local validator.
	pub fn n_assignments(&self) -> usize {
		self.assigned_validators.count_ones()
	}

	/// Get the backing group index of the approval entry.
	pub fn backing_group(&self) -> GroupIndex {
		self.backing_group
	}

	/// Get the assignment cert & approval signature.
	///
	/// The approval signature will only be `Some` if the assignment is too.
	pub fn local_statements(&self) -> (Option<OurAssignment>, Option<OurApproval>) {
		let approval_sig = self.our_approval_sig.clone();
		if let Some(our_assignment) = self.our_assignment.as_ref().filter(|a| a.triggered()) {
			(Some(our_assignment.clone()), approval_sig)
		} else {
			(None, None)
		}
	}

	// Convert an ApprovalEntry from v1 version to latest version
	pub fn from_v1(
		value: crate::approval_db::v1::ApprovalEntry,
		candidate_index: CandidateIndex,
	) -> Self {
		ApprovalEntry {
			tranches: value.tranches.into_iter().map(|tranche| tranche.into()).collect(),
			backing_group: value.backing_group,
			our_assignment: value.our_assignment.map(|assignment| assignment.into()),
			our_approval_sig: value
				.our_approval_sig
				.map(|sig| OurApproval::from_v1(sig, candidate_index)),
			assigned_validators: value.assignments,
			approved: value.approved,
		}
	}

	// Convert an ApprovalEntry from v1 version to latest version
	pub fn from_v2(
		value: crate::approval_db::v2::ApprovalEntry,
		candidate_index: CandidateIndex,
	) -> Self {
		ApprovalEntry {
			tranches: value.tranches.into_iter().map(|tranche| tranche.into()).collect(),
			backing_group: value.backing_group,
			our_assignment: value.our_assignment.map(|assignment| assignment.into()),
			our_approval_sig: value
				.our_approval_sig
				.map(|sig| OurApproval::from_v2(sig, candidate_index)),
			assigned_validators: value.assigned_validators,
			approved: value.approved,
		}
	}
}

impl From<crate::approval_db::v3::ApprovalEntry> for ApprovalEntry {
	fn from(entry: crate::approval_db::v3::ApprovalEntry) -> Self {
		ApprovalEntry {
			tranches: entry.tranches.into_iter().map(Into::into).collect(),
			backing_group: entry.backing_group,
			our_assignment: entry.our_assignment.map(Into::into),
			our_approval_sig: entry.our_approval_sig.map(Into::into),
			assigned_validators: entry.assigned_validators,
			approved: entry.approved,
		}
	}
}

impl From<ApprovalEntry> for crate::approval_db::v3::ApprovalEntry {
	fn from(entry: ApprovalEntry) -> Self {
		Self {
			tranches: entry.tranches.into_iter().map(Into::into).collect(),
			backing_group: entry.backing_group,
			our_assignment: entry.our_assignment.map(Into::into),
			our_approval_sig: entry.our_approval_sig.map(Into::into),
			assigned_validators: entry.assigned_validators,
			approved: entry.approved,
		}
	}
}

/// Metadata regarding approval of a particular candidate.
#[derive(Debug, Clone, PartialEq)]
pub struct CandidateEntry {
	pub candidate: CandidateReceipt,
	pub session: SessionIndex,
	// Assignments are based on blocks, so we need to track assignments separately
	// based on the block we are looking at.
	pub block_assignments: BTreeMap<Hash, ApprovalEntry>,
	pub approvals: Bitfield,
}

impl CandidateEntry {
	/// Access the bit-vec of approvals.
	pub fn approvals(&self) -> &BitSlice<u8, BitOrderLsb0> {
		&self.approvals
	}

	/// Note that a given validator has approved. Return the previous approval state.
	pub fn mark_approval(&mut self, validator: ValidatorIndex) -> bool {
		let prev = self.has_approved(validator);
		self.approvals.set(validator.0 as usize, true);
		prev
	}

	/// Query whether a given validator has approved the candidate.
	pub fn has_approved(&self, validator: ValidatorIndex) -> bool {
		self.approvals.get(validator.0 as usize).map(|b| *b).unwrap_or(false)
	}

	/// Get the candidate receipt.
	pub fn candidate_receipt(&self) -> &CandidateReceipt {
		&self.candidate
	}

	/// Get the approval entry, mutably, for this candidate under a specific block.
	pub fn approval_entry_mut(&mut self, block_hash: &Hash) -> Option<&mut ApprovalEntry> {
		self.block_assignments.get_mut(block_hash)
	}

	/// Get the approval entry for this candidate under a specific block.
	pub fn approval_entry(&self, block_hash: &Hash) -> Option<&ApprovalEntry> {
		self.block_assignments.get(block_hash)
	}

	/// Convert a CandidateEntry from a v1 to its latest equivalent.
	pub fn from_v1(
		value: crate::approval_db::v1::CandidateEntry,
		candidate_index: CandidateIndex,
	) -> Self {
		Self {
			approvals: value.approvals,
			block_assignments: value
				.block_assignments
				.into_iter()
				.map(|(h, ae)| (h, ApprovalEntry::from_v1(ae, candidate_index)))
				.collect(),
			candidate: value.candidate,
			session: value.session,
		}
	}

	/// Convert a CandidateEntry from a v2 to its latest equivalent.
	pub fn from_v2(
		value: crate::approval_db::v2::CandidateEntry,
		candidate_index: CandidateIndex,
	) -> Self {
		Self {
			approvals: value.approvals,
			block_assignments: value
				.block_assignments
				.into_iter()
				.map(|(h, ae)| (h, ApprovalEntry::from_v2(ae, candidate_index)))
				.collect(),
			candidate: value.candidate,
			session: value.session,
		}
	}
}

impl From<crate::approval_db::v3::CandidateEntry> for CandidateEntry {
	fn from(entry: crate::approval_db::v3::CandidateEntry) -> Self {
		CandidateEntry {
			candidate: entry.candidate,
			session: entry.session,
			block_assignments: entry
				.block_assignments
				.into_iter()
				.map(|(h, ae)| (h, ae.into()))
				.collect(),
			approvals: entry.approvals,
		}
	}
}

impl From<CandidateEntry> for crate::approval_db::v3::CandidateEntry {
	fn from(entry: CandidateEntry) -> Self {
		Self {
			candidate: entry.candidate,
			session: entry.session,
			block_assignments: entry
				.block_assignments
				.into_iter()
				.map(|(h, ae)| (h, ae.into()))
				.collect(),
			approvals: entry.approvals,
		}
	}
}

/// Metadata regarding approval of a particular block, by way of approval of the
/// candidates contained within it.
#[derive(Debug, Clone, PartialEq)]
pub struct BlockEntry {
	block_hash: Hash,
	parent_hash: Hash,
	block_number: BlockNumber,
	session: SessionIndex,
	slot: Slot,
	relay_vrf_story: RelayVRFStory,
	// The candidates included as-of this block and the index of the core they are
	// leaving.
	candidates: Vec<(CoreIndex, CandidateHash)>,
	// A bitfield where the i'th bit corresponds to the i'th candidate in `candidates`.
	// The i'th bit is `true` iff the candidate has been approved in the context of this
	// block. The block can be considered approved if the bitfield has all bits set to `true`.
	pub approved_bitfield: Bitfield,
	pub children: Vec<Hash>,
	// A list of candidates we have checked, but didn't not sign and
	// advertise the vote yet.
	candidates_pending_signature: BTreeMap<CandidateIndex, CandidateSigningContext>,
	// A list of assignments for which we already distributed the assignment.
	// We use this to ensure we don't distribute multiple core assignments twice as we track
	// individual wakeups for each core.
	distributed_assignments: Bitfield,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CandidateSigningContext {
	pub candidate_hash: CandidateHash,
	pub sign_no_later_than_tick: Tick,
}

impl BlockEntry {
	/// Mark a candidate as fully approved in the bitfield.
	pub fn mark_approved_by_hash(&mut self, candidate_hash: &CandidateHash) {
		if let Some(p) = self.candidates.iter().position(|(_, h)| h == candidate_hash) {
			self.approved_bitfield.set(p, true);
		}
	}

	/// Whether a candidate is approved in the bitfield.
	pub fn is_candidate_approved(&self, candidate_hash: &CandidateHash) -> bool {
		self.candidates
			.iter()
			.position(|(_, h)| h == candidate_hash)
			.and_then(|p| self.approved_bitfield.get(p).map(|b| *b))
			.unwrap_or(false)
	}

	/// Whether the block entry is fully approved.
	pub fn is_fully_approved(&self) -> bool {
		self.approved_bitfield.all()
	}

	/// Iterate over all unapproved candidates.
	pub fn unapproved_candidates(&self) -> impl Iterator<Item = CandidateHash> + '_ {
		self.approved_bitfield.iter().enumerate().filter_map(move |(i, a)| {
			if !*a {
				Some(self.candidates[i].1)
			} else {
				None
			}
		})
	}

	/// Get the slot of the block.
	pub fn slot(&self) -> Slot {
		self.slot
	}

	/// Get the relay-vrf-story of the block.
	pub fn relay_vrf_story(&self) -> RelayVRFStory {
		self.relay_vrf_story.clone()
	}

	/// Get the session index of the block.
	pub fn session(&self) -> SessionIndex {
		self.session
	}

	/// Get the i'th candidate.
	pub fn candidate(&self, i: usize) -> Option<&(CoreIndex, CandidateHash)> {
		self.candidates.get(i)
	}

	/// Access the underlying candidates as a slice.
	pub fn candidates(&self) -> &[(CoreIndex, CandidateHash)] {
		&self.candidates
	}

	/// Access the block number of the block entry.
	pub fn block_number(&self) -> BlockNumber {
		self.block_number
	}

	/// Access the block hash of the block entry.
	pub fn block_hash(&self) -> Hash {
		self.block_hash
	}

	/// Access the parent hash of the block entry.
	pub fn parent_hash(&self) -> Hash {
		self.parent_hash
	}

	/// Mark distributed assignment for many candidate indices.
	/// Returns `true` if an assignment was already distributed for the `candidates`.
	pub fn mark_assignment_distributed(&mut self, candidates: CandidateBitfield) -> bool {
		let bitfield = candidates.into_inner();
		let total_one_bits = self.distributed_assignments.count_ones();

		let new_len = std::cmp::max(self.distributed_assignments.len(), bitfield.len());
		self.distributed_assignments.resize(new_len, false);
		self.distributed_assignments |= bitfield;

		// If an operation did not change our current bitfield, we return true.
		let distributed = total_one_bits == self.distributed_assignments.count_ones();

		distributed
	}

	/// Defer signing and issuing an approval for a candidate no later than the specified tick
	pub fn defer_candidate_signature(
		&mut self,
		candidate_index: CandidateIndex,
		candidate_hash: CandidateHash,
		sign_no_later_than_tick: Tick,
	) -> Option<CandidateSigningContext> {
		self.candidates_pending_signature.insert(
			candidate_index,
			CandidateSigningContext { candidate_hash, sign_no_later_than_tick },
		)
	}

	/// Returns the number of candidates waiting for an approval to be issued.
	pub fn num_candidates_pending_signature(&self) -> usize {
		self.candidates_pending_signature.len()
	}

	/// Return if we have candidates waiting for signature to be issued
	pub fn has_candidates_pending_signature(&self) -> bool {
		!self.candidates_pending_signature.is_empty()
	}

	/// Returns true if candidate hash is in the queue for a signature.
	pub fn candidate_is_pending_signature(&self, candidate_hash: CandidateHash) -> bool {
		self.candidates_pending_signature
			.values()
			.any(|context| context.candidate_hash == candidate_hash)
	}

	/// Candidate hashes  for candidates pending signatures
	fn candidate_hashes_pending_signature(&self) -> Vec<CandidateHash> {
		self.candidates_pending_signature
			.values()
			.map(|unsigned_approval| unsigned_approval.candidate_hash)
			.collect()
	}

	/// Candidate indices for candidates pending signature
	fn candidate_indices_pending_signature(&self) -> Option<CandidateBitfield> {
		self.candidates_pending_signature
			.keys()
			.map(|val| *val)
			.collect_vec()
			.try_into()
			.ok()
	}

	/// Returns a list of candidates hashes that need need signature created at the current tick:
	/// This might happen in other of the two reasons:
	/// 1. We queued more than max_approval_coalesce_count candidates.
	/// 2. We have candidates that waiting in the queue past their `sign_no_later_than_tick`
	///
	/// Additionally, we also return the first tick when we will have to create a signature,
	/// so that the caller can arm the timer if it is not already armed.
	pub fn get_candidates_that_need_signature(
		&self,
		tick_now: Tick,
		max_approval_coalesce_count: u32,
	) -> (Option<(Vec<CandidateHash>, CandidateBitfield)>, Option<Tick>) {
		let sign_no_later_than_tick = self
			.candidates_pending_signature
			.values()
			.min_by(|a, b| a.sign_no_later_than_tick.cmp(&b.sign_no_later_than_tick))
			.map(|val| val.sign_no_later_than_tick);

		if let Some(sign_no_later_than_tick) = sign_no_later_than_tick {
			if sign_no_later_than_tick <= tick_now ||
				self.num_candidates_pending_signature() >= max_approval_coalesce_count as usize
			{
				(
					self.candidate_indices_pending_signature().and_then(|candidate_indices| {
						Some((self.candidate_hashes_pending_signature(), candidate_indices))
					}),
					Some(sign_no_later_than_tick),
				)
			} else {
				// We can still wait for other candidates to queue in, so just make sure
				// we wake up at the tick we have to sign the longest waiting candidate.
				(Default::default(), Some(sign_no_later_than_tick))
			}
		} else {
			// No cached candidates, nothing to do here, this just means the timer fired,
			// but the signatures were already sent because we gathered more than
			// max_approval_coalesce_count.
			(Default::default(), sign_no_later_than_tick)
		}
	}

	/// Clears the candidates pending signature because the approval was issued.
	pub fn issued_approval(&mut self) {
		self.candidates_pending_signature.clear();
	}
}

impl From<crate::approval_db::v3::BlockEntry> for BlockEntry {
	fn from(entry: crate::approval_db::v3::BlockEntry) -> Self {
		BlockEntry {
			block_hash: entry.block_hash,
			parent_hash: entry.parent_hash,
			block_number: entry.block_number,
			session: entry.session,
			slot: entry.slot,
			relay_vrf_story: RelayVRFStory(entry.relay_vrf_story),
			candidates: entry.candidates,
			approved_bitfield: entry.approved_bitfield,
			children: entry.children,
			candidates_pending_signature: entry
				.candidates_pending_signature
				.into_iter()
				.map(|(candidate_index, signing_context)| (candidate_index, signing_context.into()))
				.collect(),
			distributed_assignments: entry.distributed_assignments,
		}
	}
}

impl From<crate::approval_db::v1::BlockEntry> for BlockEntry {
	fn from(entry: crate::approval_db::v1::BlockEntry) -> Self {
		BlockEntry {
			block_hash: entry.block_hash,
			parent_hash: entry.parent_hash,
			block_number: entry.block_number,
			session: entry.session,
			slot: entry.slot,
			relay_vrf_story: RelayVRFStory(entry.relay_vrf_story),
			candidates: entry.candidates,
			approved_bitfield: entry.approved_bitfield,
			children: entry.children,
			distributed_assignments: Default::default(),
			candidates_pending_signature: Default::default(),
		}
	}
}

impl From<crate::approval_db::v2::BlockEntry> for BlockEntry {
	fn from(entry: crate::approval_db::v2::BlockEntry) -> Self {
		BlockEntry {
			block_hash: entry.block_hash,
			parent_hash: entry.parent_hash,
			block_number: entry.block_number,
			session: entry.session,
			slot: entry.slot,
			relay_vrf_story: RelayVRFStory(entry.relay_vrf_story),
			candidates: entry.candidates,
			approved_bitfield: entry.approved_bitfield,
			children: entry.children,
			distributed_assignments: entry.distributed_assignments,
			candidates_pending_signature: Default::default(),
		}
	}
}

impl From<BlockEntry> for crate::approval_db::v3::BlockEntry {
	fn from(entry: BlockEntry) -> Self {
		Self {
			block_hash: entry.block_hash,
			parent_hash: entry.parent_hash,
			block_number: entry.block_number,
			session: entry.session,
			slot: entry.slot,
			relay_vrf_story: entry.relay_vrf_story.0,
			candidates: entry.candidates,
			approved_bitfield: entry.approved_bitfield,
			children: entry.children,
			candidates_pending_signature: entry
				.candidates_pending_signature
				.into_iter()
				.map(|(candidate_index, signing_context)| (candidate_index, signing_context.into()))
				.collect(),
			distributed_assignments: entry.distributed_assignments,
		}
	}
}

impl From<crate::approval_db::v3::CandidateSigningContext> for CandidateSigningContext {
	fn from(signing_context: crate::approval_db::v3::CandidateSigningContext) -> Self {
		Self {
			candidate_hash: signing_context.candidate_hash,
			sign_no_later_than_tick: signing_context.sign_no_later_than_tick.into(),
		}
	}
}

impl From<CandidateSigningContext> for crate::approval_db::v3::CandidateSigningContext {
	fn from(signing_context: CandidateSigningContext) -> Self {
		Self {
			candidate_hash: signing_context.candidate_hash,
			sign_no_later_than_tick: signing_context.sign_no_later_than_tick.into(),
		}
	}
}
