// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use futures::channel::oneshot;

use sc_consensus::{BlockImportError, BlockImportStatus};
use sc_network::{
	config::MultiaddrWithPeerId,
	request_responses::{IfDisconnected, RequestFailure},
	types::ProtocolName,
	NetworkPeers, NetworkRequest, NetworkSyncForkRequest, ReputationChange,
};
use sc_network_common::role::ObservedRole;
use sc_network_types::{multiaddr::Multiaddr, PeerId};
use sp_runtime::traits::{Block as BlockT, NumberFor};

use std::collections::HashSet;

mockall::mock! {
	pub ChainSyncInterface<B: BlockT> {
		pub fn justification_sync_link_request_justification(&self, hash: &B::Hash, number: NumberFor<B>);
		pub fn justification_sync_link_clear_justification_requests(&self);
	}

	impl<B: BlockT + 'static> NetworkSyncForkRequest<B::Hash, NumberFor<B>>
		for ChainSyncInterface<B>
	{
		fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: B::Hash, number: NumberFor<B>);
	}

	impl<B: BlockT> sc_consensus::Link<B> for ChainSyncInterface<B> {
		fn blocks_processed(
			&self,
			imported: usize,
			count: usize,
			results: Vec<(Result<BlockImportStatus<NumberFor<B>>, BlockImportError>, B::Hash)>,
		);
		fn justification_imported(
			&self,
			who: PeerId,
			hash: &B::Hash,
			number: NumberFor<B>,
			import_result: sc_consensus::JustificationImportResult,
		);
		fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>);
	}
}

impl<B: BlockT> sc_consensus::JustificationSyncLink<B> for MockChainSyncInterface<B> {
	fn request_justification(&self, hash: &B::Hash, number: NumberFor<B>) {
		self.justification_sync_link_request_justification(hash, number);
	}

	fn clear_justification_requests(&self) {
		self.justification_sync_link_clear_justification_requests();
	}
}

mockall::mock! {
	pub NetworkServiceHandle {}
}

// Mocked `Network` for `ChainSync`-related tests
mockall::mock! {
	pub Network {}

	#[async_trait::async_trait]
	impl NetworkPeers for Network {
		fn set_authorized_peers(&self, peers: HashSet<PeerId>);
		fn set_authorized_only(&self, reserved_only: bool);
		fn add_known_address(&self, peer_id: PeerId, addr: Multiaddr);
		fn report_peer(&self, peer_id: PeerId, cost_benefit: ReputationChange);
		fn peer_reputation(&self, peer_id: &PeerId) -> i32;
		fn disconnect_peer(&self, peer_id: PeerId, protocol: ProtocolName);
		fn accept_unreserved_peers(&self);
		fn deny_unreserved_peers(&self);
		fn add_reserved_peer(&self, peer: MultiaddrWithPeerId) -> Result<(), String>;
		fn remove_reserved_peer(&self, peer_id: PeerId);
		fn set_reserved_peers(
			&self,
			protocol: ProtocolName,
			peers: HashSet<Multiaddr>,
		) -> Result<(), String>;
		fn add_peers_to_reserved_set(
			&self,
			protocol: ProtocolName,
			peers: HashSet<Multiaddr>,
		) -> Result<(), String>;
		fn remove_peers_from_reserved_set(
			&self,
			protocol: ProtocolName,
			peers: Vec<PeerId>
		) -> Result<(), String>;
		fn sync_num_connected(&self) -> usize;
		fn peer_role(&self, peer_id: PeerId, handshake: Vec<u8>) -> Option<ObservedRole>;
		async fn reserved_peers(&self) -> Result<Vec<sc_network_types::PeerId>, ()>;
	}

	#[async_trait::async_trait]
	impl NetworkRequest for Network {
		async fn request(
			&self,
			target: PeerId,
			protocol: ProtocolName,
			request: Vec<u8>,
			fallback_request: Option<(Vec<u8>, ProtocolName)>,
			connect: IfDisconnected,
		) -> Result<(Vec<u8>, ProtocolName), RequestFailure>;
		fn start_request(
			&self,
			target: PeerId,
			protocol: ProtocolName,
			request: Vec<u8>,
			fallback_request: Option<(Vec<u8>, ProtocolName)>,
			tx: oneshot::Sender<Result<(Vec<u8>, ProtocolName), RequestFailure>>,
			connect: IfDisconnected,
		);
	}
}
