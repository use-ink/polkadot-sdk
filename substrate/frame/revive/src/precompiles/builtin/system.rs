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
	precompiles::{BuiltinAddressMatcher, BuiltinPrecompile, Error, Ext},
	vm::RuntimeCosts,
	Config,
};
use alloc::vec::Vec;
use alloy_core::sol;
use alloy_core::sol_types::SolValue;
use core::{marker::PhantomData, num::NonZero};
use sp_core::hexdisplay::AsBytesRef;

pub struct System<T>(PhantomData<T>);

sol! {
	interface ISystem {
		/// Computes the BLAKE2 256-bit hash on the given input.
		function hashBlake256(bytes memory input) external pure returns (bytes32 digest);
		/// Computes the BLAKE2 128-bit hash on the given input.
		function hashBlake128(bytes memory input) external pure returns (bytes32 digest);
		/// Retrieve the account id for a specified `H160` address.
		///
		/// Calling this function on a native `H160` chain (`type AccountId = H160`)
		/// does not make sense, as it would just return the `address` that it was
		/// called with.
		///
		/// # Note
		///
		/// If no mapping exists for `addr`, the fallback account id will be returned.
		function toAccountId(address input) external view returns (bytes memory account_id);
		/// Calculates the Ethereum address from the ECDSA compressed public key.
		///
		/// # Parameters
		///
		/// - `pubkey`: The public key bytes.
		/// - `output`: A reference to the output data buffer to write the address.
		///
		/// # Returns
		///
		/// Returns an empty Vector if the ECDSA public key recovery failed.
		/// Most probably because of a wrong recovery id or signature.
		function ecdsaToEthAddress(bytes memory pubkey)
			external pure returns (address);
		/// Verify a sr25519 signature
		///
		/// # Parameters
		///
		/// - `signature`: The signature bytes.
		/// - `message`: The message bytes.
		///
		/// # Returns
		///
		/// `true` if verification successful, `false` otherwise.
		function sr25519Verify(bytes32[2] signature, bytes32 pubkey, bytes memory message)
			external pure returns (bool);
	}
}

impl<T: Config> BuiltinPrecompile for System<T> {
	type T = T;
	type Interface = ISystem::ISystemCalls;
	const MATCHER: BuiltinAddressMatcher =
		BuiltinAddressMatcher::Fixed(NonZero::new(0x900).unwrap());
	const HAS_CONTRACT_INFO: bool = false;

	fn call(
		_address: &[u8; 20],
		input: &Self::Interface,
		env: &mut impl Ext<T = Self::T>,
	) -> Result<Vec<u8>, Error> {
		log::info!(target: crate::LOG_TARGET, "-------------------0");
		use ISystem::ISystemCalls;
		match input {
			ISystemCalls::hashBlake256(ISystem::hashBlake256Call { input }) => {
				env.gas_meter_mut().charge(RuntimeCosts::HashBlake256(input.len() as u32))?;
				let output = sp_io::hashing::blake2_256(input.as_bytes_ref());
				Ok(output.to_vec())
			},
			ISystemCalls::hashBlake128(ISystem::hashBlake128Call { input }) => {
				env.gas_meter_mut().charge(RuntimeCosts::HashBlake128(input.len() as u32))?;
				let output = sp_io::hashing::blake2_128(input.as_bytes_ref());
				Ok(output.to_vec())
			},
			ISystemCalls::toAccountId(ISystem::toAccountIdCall { input }) => {
				use crate::address::AddressMapper;
				use codec::Encode;
				env.gas_meter_mut().charge(RuntimeCosts::ToAccountId)?;
				let account_id =
					T::AddressMapper::to_account_id(&crate::H160::from_slice(input.as_slice()));
				Ok(account_id.encode())
			},
			ISystemCalls::ecdsaToEthAddress(ISystem::ecdsaToEthAddressCall { pubkey }) => {
				env.gas_meter_mut().charge(RuntimeCosts::EcdsaToEthAddress)?;
				let foo: &[u8] = pubkey.as_ref();
				let ret = match env.ecdsa_to_eth_address(foo.try_into().unwrap()) {
					Ok(ret) => ret,
					Err(_) => [0u8; 20]
				};
				Ok(ret.abi_encode())
			},
			ISystemCalls::sr25519Verify(ISystem::sr25519VerifyCall { signature, pubkey, message }) => {
				log::info!(target: crate::LOG_TARGET, "-------------------1");
				env.gas_meter_mut().charge(RuntimeCosts::Sr25519Verify(message.len() as u32))?;
				//let sig = <&[alloy_core::primitives::FixedBytes<1>; 64] as Into<T>>::into(signature);
				//let mut sig = [0u8; 64];
				//signature.
				//let signature = signature.0;

				log::info!(target: crate::LOG_TARGET, "-------------------2");
				let mut sig = [0u8; 64];
				sig[..32].copy_from_slice(&signature[0][..32]);
				sig[32..].copy_from_slice(&signature[1][..32]);
				/*
				for (i, b) in signature.iter().enumerate() {
					sig[i] = b[0];
				}
				 */
				log::info!(target: crate::LOG_TARGET, "-------------------3");
				let ret = env.sr25519_verify(&sig, &message, &pubkey);
				log::info!(target: crate::LOG_TARGET, "-------------------4");
				Ok(ret.abi_encode())
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{ISystem, *};
	use crate::{
		address::AddressMapper,
		call_builder::{caller_funding, CallSetup},
		pallet,
		precompiles::{tests::run_test_vectors, BuiltinPrecompile},
		tests::{ExtBuilder, Test},
		H160,
	};
	use codec::Decode;
	use frame_support::traits::fungible::Mutate;

	#[test]
	fn test_system_precompile() {
		run_test_vectors::<System<Test>>(include_str!("testdata/900-blake2_256.json"));
		run_test_vectors::<System<Test>>(include_str!("testdata/900-blake2_128.json"));
		run_test_vectors::<System<Test>>(include_str!("testdata/900-to_account_id.json"));
	}

	#[test]
	fn test_system_precompile_unmapped_account() {
		ExtBuilder::default().build().execute_with(|| {
			// given
			let mut call_setup = CallSetup::<Test>::default();
			let (mut ext, _) = call_setup.ext();
			let unmapped_address = H160::zero();

			// when
			let input = ISystem::ISystemCalls::toAccountId(ISystem::toAccountIdCall {
				input: unmapped_address.0.into(),
			});
			let expected_fallback_account_id =
				<System<Test>>::call(&<System<Test>>::MATCHER.base_address(), &input, &mut ext)
					.unwrap();

			// then
			assert_eq!(
				expected_fallback_account_id[20..32],
				[0xEE; 12],
				"no fallback suffix found where one should be"
			);
		})
	}

	#[test]
	fn test_system_precompile_mapped_account() {
		use crate::test_utils::EVE;
		ExtBuilder::default().build().execute_with(|| {
			// given
			let mapped_address = {
				<Test as pallet::Config>::Currency::set_balance(&EVE, caller_funding::<Test>());
				let _ = <Test as pallet::Config>::AddressMapper::map(&EVE);
				<Test as pallet::Config>::AddressMapper::to_address(&EVE)
			};

			let mut call_setup = CallSetup::<Test>::default();
			let (mut ext, _) = call_setup.ext();

			// when
			let input = ISystem::ISystemCalls::toAccountId(ISystem::toAccountIdCall {
				input: mapped_address.0.into(),
			});
			let data =
				<System<Test>>::call(&<System<Test>>::MATCHER.base_address(), &input, &mut ext)
					.unwrap();

			// then
			assert_ne!(
				data.as_slice()[20..32],
				[0xEE; 12],
				"fallback suffix found where none should be"
			);
			assert_eq!(
				<Test as frame_system::Config>::AccountId::decode(&mut data.as_slice()),
				Ok(EVE),
			);
		})
	}
}
