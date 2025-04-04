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
//

//! Error handling related code and Error/Result definitions.

use futures::channel::oneshot;

use polkadot_node_network_protocol::request_response::incoming;
use polkadot_node_primitives::UncheckedSignedFullStatement;
use polkadot_node_subsystem::{errors::SubsystemError, RuntimeApiError};
use polkadot_node_subsystem_util::{backing_implicit_view, runtime};
use polkadot_primitives::vstaging::CandidateDescriptorVersion;

use crate::LOG_TARGET;

/// General result.
pub type Result<T> = std::result::Result<T, Error>;

use fatality::Nested;

#[allow(missing_docs)]
#[fatality::fatality(splitable)]
pub enum Error {
	#[fatal]
	#[error("Receiving message from overseer failed")]
	SubsystemReceive(#[from] SubsystemError),

	#[fatal(forward)]
	#[error("Retrieving next incoming request failed")]
	IncomingRequest(#[from] incoming::Error),

	#[fatal(forward)]
	#[error("Error while accessing runtime information")]
	Runtime(#[from] runtime::Error),

	#[error("Error while accessing Runtime API")]
	RuntimeApi(#[from] RuntimeApiError),

	#[error(transparent)]
	ImplicitViewFetchError(backing_implicit_view::FetchError),

	#[error("Response receiver for active validators request cancelled")]
	CancelledActiveValidators(oneshot::Canceled),

	#[error("Response receiver for validator groups request cancelled")]
	CancelledValidatorGroups(oneshot::Canceled),

	#[error("Response receiver for availability cores request cancelled")]
	CancelledAvailabilityCores(oneshot::Canceled),

	#[error("CollationSeconded contained statement with invalid signature")]
	InvalidStatementSignature(UncheckedSignedFullStatement),

	#[error("Response receiver for session index request cancelled")]
	CancelledSessionIndex(oneshot::Canceled),

	#[error("Response receiver for claim queue request cancelled")]
	CancelledClaimQueue(oneshot::Canceled),

	#[error("Response receiver for node features request cancelled")]
	CancelledNodeFeatures(oneshot::Canceled),

	#[error("No state for the relay parent")]
	RelayParentStateNotFound,
}

/// An error happened on the validator side of the protocol when attempting
/// to start seconding a candidate.
#[derive(Debug, thiserror::Error)]
pub enum SecondingError {
	#[error("Error while accessing Runtime API")]
	RuntimeApi(#[from] RuntimeApiError),

	#[error("Response receiver for persisted validation data request cancelled")]
	CancelledRuntimePersistedValidationData(oneshot::Canceled),

	#[error("Response receiver for prospective validation data request cancelled")]
	CancelledProspectiveValidationData(oneshot::Canceled),

	#[error("Persisted validation data is not available")]
	PersistedValidationDataNotFound,

	#[error("Persisted validation data hash doesn't match one in the candidate receipt.")]
	PersistedValidationDataMismatch,

	#[error("Candidate hash doesn't match the advertisement")]
	CandidateHashMismatch,

	#[error("Relay parent hash doesn't match the advertisement")]
	RelayParentMismatch,

	#[error("Received duplicate collation from the peer")]
	Duplicate,

	#[error("The provided parent head data does not match the hash")]
	ParentHeadDataMismatch,

	#[error("Core index {0} present in descriptor is different than the assigned core {1}")]
	InvalidCoreIndex(u32, u32),

	#[error("Session index {0} present in descriptor is different than the expected one {1}")]
	InvalidSessionIndex(u32, u32),

	#[error("Invalid candidate receipt version {0:?}")]
	InvalidReceiptVersion(CandidateDescriptorVersion),
}

impl SecondingError {
	/// Returns true if an error indicates that a peer is malicious.
	pub fn is_malicious(&self) -> bool {
		use SecondingError::*;
		matches!(
			self,
			PersistedValidationDataMismatch |
				CandidateHashMismatch |
				RelayParentMismatch |
				ParentHeadDataMismatch |
				InvalidCoreIndex(_, _) |
				InvalidSessionIndex(_, _) |
				InvalidReceiptVersion(_)
		)
	}
}

/// A validator failed to request a collation due to an error.
#[derive(Debug, thiserror::Error)]
pub enum FetchError {
	#[error("Collation was not previously advertised")]
	NotAdvertised,

	#[error("Peer is unknown")]
	UnknownPeer,

	#[error("Collation was already requested")]
	AlreadyRequested,

	#[error("Relay parent went out of view")]
	RelayParentOutOfView,

	#[error("Peer's protocol doesn't match the advertisement")]
	ProtocolMismatch,
}

/// Utility for eating top level errors and log them.
///
/// We basically always want to try and continue on error. This utility function is meant to
/// consume top-level errors by simply logging them.
pub fn log_error(result: Result<()>, ctx: &'static str) -> std::result::Result<(), FatalError> {
	match result.into_nested()? {
		Ok(()) => Ok(()),
		Err(jfyi) => {
			gum::warn!(target: LOG_TARGET, error = ?jfyi, ctx);
			Ok(())
		},
	}
}
