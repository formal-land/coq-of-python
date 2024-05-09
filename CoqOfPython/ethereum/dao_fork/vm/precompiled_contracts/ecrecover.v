Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) ECRECOVER PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the ECRECOVER precompiled contract.
".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".

Require ethereum.crypto.elliptic_curve.
Axiom ethereum_crypto_elliptic_curve_SECP256K1N :
  IsGlobalAlias globals ethereum.crypto.elliptic_curve.globals "SECP256K1N".
Axiom ethereum_crypto_elliptic_curve_secp256k1_recover :
  IsGlobalAlias globals ethereum.crypto.elliptic_curve.globals "secp256k1_recover".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_Hash32 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "Hash32".
Axiom ethereum_crypto_hash_keccak256 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak256".

Require ethereum.utils.byte.
Axiom ethereum_utils_byte_left_pad_zero_bytes :
  IsGlobalAlias globals ethereum.utils.byte.globals "left_pad_zero_bytes".

Require vm.
Axiom vm_Evm :
  IsGlobalAlias globals vm.globals "Evm".

Require vm.gas.
Axiom vm_gas_GAS_ECRECOVER :
  IsGlobalAlias globals vm.gas.globals "GAS_ECRECOVER".
Axiom vm_gas_charge_gas :
  IsGlobalAlias globals vm.gas.globals "charge_gas".

Require vm.memory.
Axiom vm_memory_buffer_read :
  IsGlobalAlias globals vm.memory.globals "buffer_read".

Definition ecrecover : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Decrypts the address using elliptic curve DSA recovery mechanism and writes
    the address to output.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let data :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_ECRECOVER" |)
    ],
    make_dict []
  |) in
    let message_hash_bytes :=
      M.call (|
        M.get_name (| globals, "buffer_read" |),
        make_list [
          M.get_name (| globals, "data" |);
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 32
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let message_hash :=
      M.call (|
        M.get_name (| globals, "Hash32" |),
        make_list [
          M.get_name (| globals, "message_hash_bytes" |)
        ],
        make_dict []
      |) in
    let v :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 32
                ],
                make_dict []
              |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 32
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let r :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 64
                ],
                make_dict []
              |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 32
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let s :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 96
                ],
                make_dict []
              |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 32
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.not_eq (| M.get_name (| globals, "v" |), Constant.int 27 |),
          ltac:(M.monadic (
            Compare.not_eq (| M.get_name (| globals, "v" |), Constant.int 28 |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          (* At expr: unsupported node type: NoneType *)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.gt_e (| Constant.int 0, M.get_name (| globals, "r" |) |),
          ltac:(M.monadic (
            Compare.gt_e (| M.get_name (| globals, "r" |), M.get_name (| globals, "SECP256K1N" |) |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          (* At expr: unsupported node type: NoneType *)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.gt_e (| Constant.int 0, M.get_name (| globals, "s" |) |),
          ltac:(M.monadic (
            Compare.gt_e (| M.get_name (| globals, "s" |), M.get_name (| globals, "SECP256K1N" |) |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          (* At expr: unsupported node type: NoneType *)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
(* At stmt: unsupported node type: Try *)
    let address :=
      M.get_subscript (| M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.get_name (| globals, "public_key" |)
        ],
        make_dict []
      |), Constant.int 12:Constant.int 32 |) in
    let padded_address :=
      M.call (|
        M.get_name (| globals, "left_pad_zero_bytes" |),
        make_list [
          M.get_name (| globals, "address" |);
          Constant.int 32
        ],
        make_dict []
      |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      M.get_name (| globals, "padded_address" |)
    |) in
    M.pure Constant.None_)).
