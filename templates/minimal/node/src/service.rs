// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::cli::Consensus;
use futures::FutureExt;
use minimal_template_runtime::{interface::OpaqueBlock as Block, RuntimeApi};
use polkadot_sdk::{
	sc_client_api::backend::Backend,
	sc_consensus_manual_seal::{seal_block, SealBlockParams},
	sc_executor::WasmExecutor,
	sc_service::{error::Error as ServiceError, Configuration, TaskManager},
	sc_telemetry::{Telemetry, TelemetryWorker},
	sc_transaction_pool_api::OffchainTransactionPoolFactory,
	sp_runtime::traits::Block as BlockT,
	*,
};
use std::sync::Arc;

type HostFunctions = sp_io::SubstrateHostFunctions;

#[docify::export]
pub(crate) type FullClient =
	sc_service::TFullClient<Block, RuntimeApi, WasmExecutor<HostFunctions>>;

type FullBackend = sc_service::TFullBackend<Block>;
type FullSelectChain = sc_consensus::LongestChain<FullBackend, Block>;

/// Assembly of PartialComponents (enough to run chain ops subcommands)
pub type Service = sc_service::PartialComponents<
	FullClient,
	FullBackend,
	FullSelectChain,
	sc_consensus::DefaultImportQueue<Block>,
	sc_transaction_pool::TransactionPoolHandle<Block, FullClient>,
	Option<Telemetry>,
>;

pub fn new_partial(config: &Configuration) -> Result<Service, ServiceError> {
	let telemetry = config
		.telemetry_endpoints
		.clone()
		.filter(|x| !x.is_empty())
		.map(|endpoints| -> Result<_, sc_telemetry::Error> {
			let worker = TelemetryWorker::new(16)?;
			let telemetry = worker.handle().new_telemetry(endpoints);
			Ok((worker, telemetry))
		})
		.transpose()?;

	let executor = sc_service::new_wasm_executor(&config.executor);

	let (client, backend, keystore_container, task_manager) =
		sc_service::new_full_parts::<Block, RuntimeApi, _>(
			config,
			telemetry.as_ref().map(|(_, telemetry)| telemetry.handle()),
			executor,
		)?;
	let client = Arc::new(client);

	let telemetry = telemetry.map(|(worker, telemetry)| {
		task_manager.spawn_handle().spawn("telemetry", None, worker.run());
		telemetry
	});

	let select_chain = sc_consensus::LongestChain::new(backend.clone());

	let transaction_pool = Arc::from(
		sc_transaction_pool::Builder::new(
			task_manager.spawn_essential_handle(),
			client.clone(),
			config.role.is_authority().into(),
		)
		.with_options(config.transaction_pool.clone())
		.with_prometheus(config.prometheus_registry())
		.build(),
	);

	let import_queue = sc_consensus_manual_seal::import_queue(
		Box::new(client.clone()),
		&task_manager.spawn_essential_handle(),
		config.prometheus_registry(),
	);

	Ok(sc_service::PartialComponents {
		client,
		backend,
		task_manager,
		import_queue,
		keystore_container,
		select_chain,
		transaction_pool,
		other: (telemetry),
	})
}

/// Builds a new service for a full client.
pub async fn new_full<Network: sc_network::NetworkBackend<Block, <Block as BlockT>::Hash>>(
	config: Configuration,
	consensus: Consensus,
) -> Result<TaskManager, ServiceError> {
	let sc_service::PartialComponents {
		client,
		backend,
		mut task_manager,
		import_queue,
		keystore_container,
		select_chain,
		transaction_pool,
		other: mut telemetry,
	} = new_partial(&config)?;

	let net_config = sc_network::config::FullNetworkConfiguration::<
		Block,
		<Block as BlockT>::Hash,
		Network,
	>::new(
		&config.network,
		config.prometheus_config.as_ref().map(|cfg| cfg.registry.clone()),
	);
	let metrics = Network::register_notification_metrics(
		config.prometheus_config.as_ref().map(|cfg| &cfg.registry),
	);

	let (network, system_rpc_tx, tx_handler_controller, sync_service) =
		sc_service::build_network(sc_service::BuildNetworkParams {
			config: &config,
			net_config,
			client: client.clone(),
			transaction_pool: transaction_pool.clone(),
			spawn_handle: task_manager.spawn_handle(),
			import_queue,
			block_announce_validator_builder: None,
			warp_sync_config: None,
			block_relay: None,
			metrics,
		})?;

	if config.offchain_worker.enabled {
		let offchain_workers =
			sc_offchain::OffchainWorkers::new(sc_offchain::OffchainWorkerOptions {
				runtime_api_provider: client.clone(),
				is_validator: config.role.is_authority(),
				keystore: Some(keystore_container.keystore()),
				offchain_db: backend.offchain_storage(),
				transaction_pool: Some(OffchainTransactionPoolFactory::new(
					transaction_pool.clone(),
				)),
				network_provider: Arc::new(network.clone()),
				enable_http_requests: true,
				custom_extensions: |_| vec![],
			})?;
		task_manager.spawn_handle().spawn(
			"offchain-workers-runner",
			"offchain-worker",
			offchain_workers.run(client.clone(), task_manager.spawn_handle()).boxed(),
		);
	}

	let rpc_extensions_builder = {
		let client = client.clone();
		let pool = transaction_pool.clone();

		Box::new(move |_| {
			let deps = crate::rpc::FullDeps { client: client.clone(), pool: pool.clone() };
			crate::rpc::create_full(deps).map_err(Into::into)
		})
	};

	let prometheus_registry = config.prometheus_registry().cloned();

	let _rpc_handlers = sc_service::spawn_tasks(sc_service::SpawnTasksParams {
		network,
		client: client.clone(),
		keystore: keystore_container.keystore(),
		task_manager: &mut task_manager,
		transaction_pool: transaction_pool.clone(),
		rpc_builder: rpc_extensions_builder,
		backend,
		system_rpc_tx,
		tx_handler_controller,
		sync_service,
		config,
		telemetry: telemetry.as_mut(),
	})?;

	let mut proposer = sc_basic_authorship::ProposerFactory::new(
		task_manager.spawn_handle(),
		client.clone(),
		transaction_pool.clone(),
		prometheus_registry.as_ref(),
		telemetry.as_ref().map(|x| x.handle()),
	);

	match consensus {
		Consensus::InstantSeal => {
			// Seal a first block to trigger fork-aware txpool `maintain`, and create a first
			// view. This is necessary so that sending txs will not keep them in mempool for
			// an undeterminated amount of time.
			//
			// If single state txpool is used there's no issue if we're sealing a first block in
			// advance.
			let create_inherent_data_providers =
				|_, ()| async move { Ok(sp_timestamp::InherentDataProvider::from_system_time()) };
			let mut client_mut = client.clone();
			let consensus_data_provider = None;
			let seal_params = SealBlockParams {
				sender: None,
				parent_hash: None,
				finalize: true,
				create_empty: true,
				env: &mut proposer,
				select_chain: &select_chain,
				block_import: &mut client_mut,
				consensus_data_provider,
				pool: transaction_pool.clone(),
				client: client.clone(),
				create_inherent_data_providers: &create_inherent_data_providers,
			};
			seal_block(seal_params).await;

			let params = sc_consensus_manual_seal::InstantSealParams {
				block_import: client.clone(),
				env: proposer,
				client,
				pool: transaction_pool,
				select_chain,
				consensus_data_provider: None,
				create_inherent_data_providers,
			};

			let authorship_future = sc_consensus_manual_seal::run_instant_seal(params);

			task_manager.spawn_essential_handle().spawn_blocking(
				"instant-seal",
				None,
				authorship_future,
			);
		},
		Consensus::ManualSeal(block_time) => {
			let (mut sink, commands_stream) = futures::channel::mpsc::channel(1024);
			task_manager.spawn_handle().spawn("block_authoring", None, async move {
				loop {
					futures_timer::Delay::new(std::time::Duration::from_millis(block_time)).await;
					sink.try_send(sc_consensus_manual_seal::EngineCommand::SealNewBlock {
						create_empty: true,
						finalize: true,
						parent_hash: None,
						sender: None,
					})
					.unwrap();
				}
			});

			let params = sc_consensus_manual_seal::ManualSealParams {
				block_import: client.clone(),
				env: proposer,
				client,
				pool: transaction_pool,
				select_chain,
				commands_stream: Box::pin(commands_stream),
				consensus_data_provider: None,
				create_inherent_data_providers: move |_, ()| async move {
					Ok(sp_timestamp::InherentDataProvider::from_system_time())
				},
			};
			let authorship_future = sc_consensus_manual_seal::run_manual_seal(params);

			task_manager.spawn_essential_handle().spawn_blocking(
				"manual-seal",
				None,
				authorship_future,
			);
		},
		_ => {},
	}

	Ok(task_manager)
}
