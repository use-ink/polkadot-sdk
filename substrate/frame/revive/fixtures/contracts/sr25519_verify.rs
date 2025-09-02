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

#![no_std]
#![no_main]

#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused)]

include!("../panic_handler.rs");
include!("../sol_utils.rs");

use uapi::{input, HostFn, HostFnImpl as api};

#[no_mangle]
#[polkavm_derive::polkavm_export]
pub extern "C" fn deploy() {}

#[no_mangle]
#[polkavm_derive::polkavm_export]
pub extern "C" fn call() {
	input!(
		signature: [u8; 64],
		pub_key: [u8; 32],
		msg: [u8; 11],
	);

	/*
	let exit_status = match api::sr25519_verify(
		&signature.try_into().unwrap(),
		msg,
		&pub_key.try_into().unwrap(),
	) {
		Ok(_) => 0u32,
		Err(code) => code as u32,
	};
	*/


	//function sr25519Verify(bytes1[64] signature, bytes32 pubkey, bytes memory message)
	let mut input = [0u8; 2048];
	let selector = solidity_selector("sr25519Verify(bytes32[2],bytes32,bytes)");
	input[..4].copy_from_slice(&selector[..4]);
	input[4..68].copy_from_slice(&signature[..64]);
	input[68..68+32].copy_from_slice(&pub_key[..32]);

	let n = encode_bytes(&msg, &mut input[68+32..]);
	//input[68+32..68+32+64].copy_from_slice(&pubkey[..32]);

	let mut out = [0u8; 32];

	let ret = api::delegate_call(
		uapi::CallFlags::empty(),
		&SYSTEM_PRECOMPILE_ADDR,
		u64::MAX,       // How much ref_time to devote for the execution. u64::MAX = use all.
		u64::MAX,       // How much proof_size to devote for the execution. u64::MAX = use all.
		&[u8::MAX; 32], // No deposit limit.
		&input[..68+32+n],
		//&input[..],
		//None,
		Some(&mut &mut out[..])
	).unwrap();

	//assert_eq!(out[31], );

	/*
	if let Err(code) = ret {
		api::return_value(uapi::ReturnFlags::REVERT, &(code as u32).to_le_bytes());
	};
	 */

	// Exit with success and take transfer return code to the output buffer.
	//api::return_value(uapi::ReturnFlags::empty(), &exit_status.to_le_bytes());
	//api::return_value(uapi::ReturnFlags::empty(), &out.to_le_bytes());
	api::return_value(uapi::ReturnFlags::empty(), &out);
}
