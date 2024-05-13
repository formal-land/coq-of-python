Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.spurious_dragon.vm.precompiled_contracts.ecrecover".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".

Axiom ethereum_crypto_elliptic_curve_imports_SECP256K1N :
  IsImported globals "ethereum.crypto.elliptic_curve" "SECP256K1N".
Axiom ethereum_crypto_elliptic_curve_imports_secp256k1_recover :
  IsImported globals "ethereum.crypto.elliptic_curve" "secp256k1_recover".

Axiom ethereum_crypto_hash_imports_Hash32 :
  IsImported globals "ethereum.crypto.hash" "Hash32".
Axiom ethereum_crypto_hash_imports_keccak256 :
  IsImported globals "ethereum.crypto.hash" "keccak256".

Axiom ethereum_utils_byte_imports_left_pad_zero_bytes :
  IsImported globals "ethereum.utils.byte" "left_pad_zero_bytes".

Axiom ethereum_spurious_dragon_vm_imports_Evm :
  IsImported globals "ethereum.spurious_dragon.vm" "Evm".

Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_ECRECOVER :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_ECRECOVER".
Axiom ethereum_spurious_dragon_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "charge_gas".

Axiom ethereum_spurious_dragon_vm_memory_imports_buffer_read :
  IsImported globals "ethereum.spurious_dragon.vm.memory" "buffer_read".

Definition ecrecover : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Decrypts the address using elliptic curve DSA recovery mechanism and writes
    the address to output.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_ECRECOVER" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "message_hash_bytes" ,
      M.call (|
        M.get_name (| globals, locals_stack, "buffer_read" |),
        make_list [
          M.get_name (| globals, locals_stack, "data" |);
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 32
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "message_hash" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Hash32" |),
        make_list [
          M.get_name (| globals, locals_stack, "message_hash_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "v" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  Constant.int 32
                ],
                make_dict []
              |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
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
      |)
    |) in
    let _ := M.assign_local (|
      "r" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  Constant.int 64
                ],
                make_dict []
              |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
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
      |)
    |) in
    let _ := M.assign_local (|
      "s" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  Constant.int 96
                ],
                make_dict []
              |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
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
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.not_eq (|
            M.get_name (| globals, locals_stack, "v" |),
            Constant.int 27
          |),
          ltac:(M.monadic (
            Compare.not_eq (|
              M.get_name (| globals, locals_stack, "v" |),
              Constant.int 28
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.None_
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
          Compare.gt_e (|
            Constant.int 0,
            M.get_name (| globals, locals_stack, "r" |)
          |),
          ltac:(M.monadic (
            Compare.gt_e (|
              M.get_name (| globals, locals_stack, "r" |),
              M.get_name (| globals, locals_stack, "SECP256K1N" |)
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.None_
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
          Compare.gt_e (|
            Constant.int 0,
            M.get_name (| globals, locals_stack, "s" |)
          |),
          ltac:(M.monadic (
            Compare.gt_e (|
              M.get_name (| globals, locals_stack, "s" |),
              M.get_name (| globals, locals_stack, "SECP256K1N" |)
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.None_
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
(* At stmt: unsupported node type: Try *)
    let _ := M.assign_local (|
      "address" ,
      M.slice (|
        M.call (|
          M.get_name (| globals, locals_stack, "keccak256" |),
          make_list [
            M.get_name (| globals, locals_stack, "public_key" |)
          ],
          make_dict []
        |),
        Constant.int 12,
        Constant.int 32,
        Constant.None_
      |)
    |) in
    let _ := M.assign_local (|
      "padded_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "left_pad_zero_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "address" |);
          Constant.int 32
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
      M.get_name (| globals, locals_stack, "padded_address" |)
    |) in
    M.pure Constant.None_)).

Axiom ecrecover_in_globals :
  IsInGlobals globals "ecrecover" (make_function ecrecover).
