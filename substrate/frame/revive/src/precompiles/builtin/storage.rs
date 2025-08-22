// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
	exec::PrecompileWithInfoExt,
	precompiles::{BuiltinAddressMatcher, BuiltinPrecompile, Error, ExtWithInfo},
	vm::{RuntimeCosts, TrapReason},
	Config, Key, SENTINEL,
};
use alloc::vec::Vec;
use alloy_core::{sol, sol_types::ContractError::Revert};
use codec::Encode;
use core::{marker::PhantomData, num::NonZero};
use frame_support::ensure;
use pallet_revive_uapi::StorageFlags;
use sp_core::hexdisplay::AsBytesRef;

pub struct Storage<T>(PhantomData<T>);

sol! {
	interface IStorage {
		/// todo
		/// Clear the value at the given key in the contract storage.
		///
		/// # Parameters
		///
		/// - `key`: The storage key.
		///
		/// # Return
		///
		/// Returns the size of the pre-existing value at the specified key if any.
		function clearStorage(uint32 flags, bytes memory key) external returns (bytes32 digest);

		/// Checks whether there is a value stored under the given key.
		///
		/// The key length must not exceed the maximum defined by the contracts module parameter.
		///
		/// # Parameters
		/// - `key`: The storage key.
		///
		/// # Return
		///
		/// Returns the size of the pre-existing value at the specified key if any.
		function containsStorage(uint32 flags, bytes memory key) external returns (bytes32 digest);

		/// Retrieve and remove the value under the given key from storage.
		///
		/// # Parameters
		/// - `key`: The storage key.
		/// - `output`: A reference to the output data buffer to write the storage entry.
		///
		/// # Errors
		///
		/// [KeyNotFound][`crate::ReturnErrorCode::KeyNotFound]
		function takeStorage(uint32 flags, bytes memory key) external returns (bytes32 digest);
	}
}

impl<T: Config> BuiltinPrecompile for Storage<T> {
	type T = T;
	type Interface = IStorage::IStorageCalls;
	const MATCHER: BuiltinAddressMatcher =
		BuiltinAddressMatcher::Fixed(NonZero::new(0x901).unwrap());
	const HAS_CONTRACT_INFO: bool = true;

	fn call_with_info(
		_address: &[u8; 20],
		input: &Self::Interface,
		env: &mut impl ExtWithInfo<T = Self::T>,
	) -> Result<Vec<u8>, Error> {
		use IStorage::IStorageCalls;
		match input {
			IStorageCalls::clearStorage(IStorage::clearStorageCall { flags, key }) => {
				// todo
				let transient = is_transient(*flags)
					.map_err(|e| Error::Revert("invalid storage flag".into()))?;
				let costs = |len| {
					if transient {
						RuntimeCosts::ClearTransientStorage(len)
					} else {
						RuntimeCosts::ClearStorage(len)
					}
				};
				let foo = env.max_value_size();
				let charged = env
					.gas_meter_mut()
					.charge(costs(foo))
					.map_err(|_| Error::Revert("failed charging gas".into()))?;
				let key = decode_key(key.as_bytes_ref(), false /* todo */)
					.map_err(|_| Error::Revert("failed decoding key".into()))?;
				let outcome = if transient {
					env.set_transient_storage(&key, None, false)
						.map_err(|_| Error::Revert("failed setting transient storage".into()))?
				} else {
					env.set_storage(&key, None, false)
						.map_err(|_| Error::Revert("failed setting storage".into()))?
				};
				env.gas_meter_mut().adjust_gas(charged, costs(outcome.old_len()));
				Ok(outcome.old_len_with_sentinel().encode())
				//Ok(vec![1])
			},
			IStorageCalls::takeStorage(IStorage::takeStorageCall { flags, key }) => {
				// todo
				/*
				let transient = Self::is_transient(flags)?;
				let costs = |len| {
					if transient {
						RuntimeCosts::TakeTransientStorage(len)
					} else {
						RuntimeCosts::TakeStorage(len)
					}
				};
				let charged = self.charge_gas(costs(self.ext.max_value_size()))?;
				let key = self.decode_key(memory, key_ptr, key_len)?;
				let outcome = if transient {
					self.ext.set_transient_storage(&key, None, true)?
				} else {
					self.ext.set_storage(&key, None, true)?
				};

				if let crate::storage::WriteOutcome::Taken(value) = outcome {
					self.adjust_gas(charged, costs(value.len() as u32));
					self.write_sandbox_output(
						memory,
						out_ptr,
						out_len_ptr,
						&value,
						false,
						already_charged,
					)?;
					Ok(ReturnErrorCode::Success)
				} else {
					self.adjust_gas(charged, costs(0));
					Ok(ReturnErrorCode::KeyNotFound)
				}

							 */
				Ok(vec![1])
			},
			IStorageCalls::containsStorage(IStorage::containsStorageCall { flags, key }) => {
				Ok(vec![1])
				// todo
				/*
				let transient = Self::is_transient(flags)?;
				let costs = |len| {
					if transient {
						RuntimeCosts::ContainsTransientStorage(len)
					} else {
						RuntimeCosts::ContainsStorage(len)
					}
				};
				let charged = self.charge_gas(costs(self.ext.max_value_size()))?;
				let key = self.decode_key(memory, key_ptr, key_len)?;
				let outcome = if transient {
					self.ext.get_transient_storage_size(&key)
				} else {
					self.ext.get_storage_size(&key)
				};
				self.adjust_gas(charged, costs(outcome.unwrap_or(0)));
				Ok(outcome.unwrap_or(SENTINEL))
							 */
			},
		}
	}
}

struct InvalidStorageFlag();
fn is_transient(flags: u32) -> Result<bool, InvalidStorageFlag> {
	StorageFlags::from_bits(flags)
		.ok_or_else(InvalidStorageFlag)
		.map(|flags| flags.contains(StorageFlags::TRANSIENT))
}

fn decode_key(key_bytes: &[u8], is_fixed_key: bool) -> Result<Key, ()> {
	match is_fixed_key {
		true => {
			if key_bytes.len() != 32 {
				return Err(());
			}
			let mut foo = [0u8; 32];
			foo[..32].copy_from_slice(&key_bytes[..32]);
			Ok(Key::from_fixed(foo))
		},
		false => {
			if key_bytes.len() as u32 > crate::limits::STORAGE_KEY_BYTES {
				return Err(());
			}
			Key::try_from_var(key_bytes.to_vec())
		},
	}
}
