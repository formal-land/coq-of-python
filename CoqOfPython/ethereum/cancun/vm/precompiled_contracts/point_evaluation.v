Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.cancun.vm.precompiled_contracts.point_evaluation".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) POINT EVALUATION PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the POINT EVALUATION precompiled contract.
".

Axiom eth2spec_deneb_mainnet_imports_KZGCommitment :
  IsImported globals "eth2spec.deneb.mainnet" "KZGCommitment".
Axiom eth2spec_deneb_mainnet_imports_kzg_commitment_to_versioned_hash :
  IsImported globals "eth2spec.deneb.mainnet" "kzg_commitment_to_versioned_hash".
Axiom eth2spec_deneb_mainnet_imports_verify_kzg_proof :
  IsImported globals "eth2spec.deneb.mainnet" "verify_kzg_proof".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".

Axiom ethereum_cancun_vm_imports_Evm :
  IsImported globals "ethereum.cancun.vm" "Evm".

Axiom ethereum_cancun_vm_exceptions_imports_KZGProofError :
  IsImported globals "ethereum.cancun.vm.exceptions" "KZGProofError".

Axiom ethereum_cancun_vm_gas_imports_GAS_POINT_EVALUATION :
  IsImported globals "ethereum.cancun.vm.gas" "GAS_POINT_EVALUATION".
Axiom ethereum_cancun_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.cancun.vm.gas" "charge_gas".

Definition FIELD_ELEMENTS_PER_BLOB : Value.t := M.run ltac:(M.monadic (
  Constant.int 4096
)).

Definition BLS_MODULUS : Value.t := M.run ltac:(M.monadic (
  Constant.int 52435875175126190479447740508185965837690552500527637822603658699938581184513
)).

Definition VERSIONED_HASH_VERSION_KZG : Value.t := M.run ltac:(M.monadic (
  Constant.bytes "01"
)).

Definition point_evaluation : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    A pre-compile that verifies a KZG proof which claims that a blob
    (represented by a commitment) evaluates to a given value at a given point.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |)
            ],
            make_dict []
          |),
          Constant.int 192
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "KZGProofError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "versioned_hash" ,
      M.slice (|
        M.get_name (| globals, locals_stack, "data" |),
        Constant.None_,
        Constant.int 32,
        Constant.None_
      |)
    |) in
    let _ := M.assign_local (|
      "z" ,
      M.slice (|
        M.get_name (| globals, locals_stack, "data" |),
        Constant.int 32,
        Constant.int 64,
        Constant.None_
      |)
    |) in
    let _ := M.assign_local (|
      "y" ,
      M.slice (|
        M.get_name (| globals, locals_stack, "data" |),
        Constant.int 64,
        Constant.int 96,
        Constant.None_
      |)
    |) in
    let _ := M.assign_local (|
      "commitment" ,
      M.call (|
        M.get_name (| globals, locals_stack, "KZGCommitment" |),
        make_list [
          M.slice (|
            M.get_name (| globals, locals_stack, "data" |),
            Constant.int 96,
            Constant.int 144,
            Constant.None_
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "proof" ,
      M.slice (|
        M.get_name (| globals, locals_stack, "data" |),
        Constant.int 144,
        Constant.int 192,
        Constant.None_
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_POINT_EVALUATION" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.call (|
            M.get_name (| globals, locals_stack, "kzg_commitment_to_versioned_hash" |),
            make_list [
              M.get_name (| globals, locals_stack, "commitment" |)
            ],
            make_dict []
          |),
          M.get_name (| globals, locals_stack, "versioned_hash" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "KZGProofError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
(* At stmt: unsupported node type: Try *)
    let _ :=
      (* if *)
      M.if_then_else (|
        UnOp.not (| M.get_name (| globals, locals_stack, "kzg_proof_verification" |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "KZGProofError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
      M.call (|
        M.get_name (| globals, locals_stack, "Bytes" |),
        make_list [
          BinOp.add (|
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  M.get_name (| globals, locals_stack, "FIELD_ELEMENTS_PER_BLOB" |)
                ],
                make_dict []
              |), "to_be_bytes32" |),
              make_list [],
              make_dict []
            |),
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  M.get_name (| globals, locals_stack, "BLS_MODULUS" |)
                ],
                make_dict []
              |), "to_be_bytes32" |),
              make_list [],
              make_dict []
            |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom point_evaluation_in_globals :
  IsInGlobals globals "point_evaluation" (make_function point_evaluation).
