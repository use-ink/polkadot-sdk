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

use async_trait::async_trait;
use codec::Encode;
use criterion::{criterion_group, criterion_main, Criterion};
use futures::executor::block_on;
use sc_transaction_pool::*;
use sp_blockchain::HashAndNumber;
use sp_crypto_hashing::blake2_256;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor},
	transaction_validity::{
		InvalidTransaction, TransactionSource, TransactionTag as Tag, TransactionValidity,
		ValidTransaction,
	},
};
use std::sync::Arc;
use substrate_test_runtime::{AccountId, Block, Extrinsic, ExtrinsicBuilder, TransferData, H256};

#[derive(Clone, Debug, Default)]
struct TestApi {
	nonce_dependant: bool,
}

impl TestApi {
	fn new_dependant() -> Self {
		TestApi { nonce_dependant: true }
	}
}

fn to_tag(nonce: u64, from: AccountId) -> Tag {
	let mut data = [0u8; 40];
	data[..8].copy_from_slice(&nonce.to_le_bytes()[..]);
	data[8..].copy_from_slice(&from.0[..]);
	data.to_vec()
}

#[async_trait]
impl ChainApi for TestApi {
	type Block = Block;
	type Error = sc_transaction_pool_api::error::Error;

	async fn validate_transaction(
		&self,
		at: <Self::Block as BlockT>::Hash,
		_: TransactionSource,
		uxt: Arc<<Self::Block as BlockT>::Extrinsic>,
		_: ValidateTransactionPriority,
	) -> Result<TransactionValidity, Self::Error> {
		let uxt = (*uxt).clone();
		let transfer = TransferData::try_from(&uxt)
			.expect("uxt is expected to be bench_call (carrying TransferData)");
		let nonce = transfer.nonce;
		let from = transfer.from;

		match self.block_id_to_number(&BlockId::Hash(at)) {
			Ok(Some(num)) if num > 5 => return Ok(Err(InvalidTransaction::Stale.into())),
			_ => {},
		}

		Ok(Ok(ValidTransaction {
			priority: 4,
			requires: if nonce > 1 && self.nonce_dependant {
				vec![to_tag(nonce - 1, from)]
			} else {
				vec![]
			},
			provides: vec![to_tag(nonce, from)],
			longevity: 10,
			propagate: true,
		}))
	}

	fn validate_transaction_blocking(
		&self,
		_at: <Self::Block as BlockT>::Hash,
		_source: TransactionSource,
		_uxt: Arc<<Self::Block as BlockT>::Extrinsic>,
	) -> Result<TransactionValidity, Self::Error> {
		unimplemented!();
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<NumberFor<Self::Block>>, Self::Error> {
		Ok(match at {
			BlockId::Number(num) => Some(*num),
			BlockId::Hash(hash) if *hash == H256::from_low_u64_be(hash.to_low_u64_be()) =>
				Some(hash.to_low_u64_be()),
			BlockId::Hash(_) => None,
		})
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<<Self::Block as BlockT>::Hash>, Self::Error> {
		Ok(match at {
			BlockId::Number(num) => Some(H256::from_low_u64_be(*num)).into(),
			BlockId::Hash(hash) => Some(*hash),
		})
	}

	fn hash_and_length(&self, uxt: &<Self::Block as BlockT>::Extrinsic) -> (H256, usize) {
		let encoded = uxt.encode();
		(blake2_256(&encoded).into(), encoded.len())
	}

	async fn block_body(
		&self,
		_id: <Self::Block as BlockT>::Hash,
	) -> Result<Option<Vec<<Self::Block as BlockT>::Extrinsic>>, Self::Error> {
		Ok(None)
	}

	fn block_header(
		&self,
		_: <Self::Block as BlockT>::Hash,
	) -> Result<Option<<Self::Block as BlockT>::Header>, Self::Error> {
		Ok(None)
	}

	fn tree_route(
		&self,
		_from: <Self::Block as BlockT>::Hash,
		_to: <Self::Block as BlockT>::Hash,
	) -> Result<sp_blockchain::TreeRoute<Self::Block>, Self::Error> {
		unimplemented!()
	}
}

fn uxt(transfer: TransferData) -> Extrinsic {
	ExtrinsicBuilder::new_bench_call(transfer).build()
}

fn bench_configured(pool: Pool<TestApi, ()>, number: u64, api: Arc<TestApi>) {
	let source = TimedTransactionSource::new_external(false);
	let mut futures = Vec::new();
	let mut tags = Vec::new();
	let at = HashAndNumber {
		hash: api.block_id_to_hash(&BlockId::Number(1)).unwrap().unwrap(),
		number: 1,
	};

	for nonce in 1..=number {
		let xt = uxt(TransferData {
			from: AccountId::from_h256(H256::from_low_u64_be(1)),
			to: AccountId::from_h256(H256::from_low_u64_be(2)),
			amount: 5,
			nonce,
		})
		.into();

		tags.push(to_tag(nonce, AccountId::from_h256(H256::from_low_u64_be(1))));

		futures.push(pool.submit_one(&at, source.clone(), xt));
	}

	let res = block_on(futures::future::join_all(futures.into_iter()));
	assert!(res.iter().all(Result::is_ok));

	assert_eq!(pool.validated_pool().status().future, 0);
	assert_eq!(pool.validated_pool().status().ready, number as usize);

	// Prune all transactions.
	let block_num = 6;
	let at = HashAndNumber {
		hash: api.block_id_to_hash(&BlockId::Number(block_num)).unwrap().unwrap(),
		number: block_num,
	};
	block_on(pool.prune_tags(&at, tags, vec![]));

	// pool is empty
	assert_eq!(pool.validated_pool().status().ready, 0);
	assert_eq!(pool.validated_pool().status().future, 0);
}

fn benchmark_main(c: &mut Criterion) {
	c.bench_function("sequential 50 tx", |b| {
		b.iter(|| {
			let api = Arc::from(TestApi::new_dependant());
			bench_configured(
				Pool::new_with_staticly_sized_rotator(Default::default(), true.into(), api.clone()),
				50,
				api,
			);
		});
	});

	c.bench_function("random 100 tx", |b| {
		b.iter(|| {
			let api = Arc::from(TestApi::default());
			bench_configured(
				Pool::new_with_staticly_sized_rotator(Default::default(), true.into(), api.clone()),
				100,
				api,
			);
		});
	});
}

criterion_group!(benches, benchmark_main);
criterion_main!(benches);
