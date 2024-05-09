Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require eth2spec.deneb.mainnet.
Axiom eth2spec_deneb_mainnet_KZGCommitment :
  IsGlobalAlias globals eth2spec.deneb.mainnet.globals "KZGCommitment".
Axiom eth2spec_deneb_mainnet_kzg_commitment_to_versioned_hash :
  IsGlobalAlias globals eth2spec.deneb.mainnet.globals "kzg_commitment_to_versioned_hash".
Axiom eth2spec_deneb_mainnet_verify_kzg_proof :
  IsGlobalAlias globals eth2spec.deneb.mainnet.globals "verify_kzg_proof".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require vm.
Axiom vm_Evm :
  IsGlobalAlias globals vm.globals "Evm".

Require vm.exceptions.
Axiom vm_exceptions_KZGProofError :
  IsGlobalAlias globals vm.exceptions.globals "KZGProofError".

Require vm.gas.
Axiom vm_gas_GAS_POINT_EVALUATION :
  IsGlobalAlias globals vm.gas.globals "GAS_POINT_EVALUATION".
Axiom vm_gas_charge_gas :
  IsGlobalAlias globals vm.gas.globals "charge_gas".

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
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    A pre-compile that verifies a KZG proof which claims that a blob
    (represented by a commitment) evaluates to a given value at a given point.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let data :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "data" |)
          ],
          make_dict []
        |),
        Constant.int 192
      |);
      M.get_name (| globals, "KZGProofError" |)
    ],
    make_dict []
  |) in
    let versioned_hash :=
      M.get_subscript (| M.get_name (| globals, "data" |), Constant.None_:Constant.int 32 |) in
    let z :=
      M.get_subscript (| M.get_name (| globals, "data" |), Constant.int 32 |) in
    let y :=
      M.get_subscript (| M.get_name (| globals, "data" |), Constant.int 64 |) in
    let commitment :=
      M.call (|
        M.get_name (| globals, "KZGCommitment" |),
        make_list [
          M.get_subscript (| M.get_name (| globals, "data" |), Constant.int 96 |)
        ],
        make_dict []
      |) in
    let proof :=
      M.get_subscript (| M.get_name (| globals, "data" |), Constant.int 144 |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_POINT_EVALUATION" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_name (| globals, "kzg_commitment_to_versioned_hash" |),
          make_list [
            M.get_name (| globals, "commitment" |)
          ],
          make_dict []
        |),
        M.get_name (| globals, "versioned_hash" |)
      |);
      M.get_name (| globals, "KZGProofError" |)
    ],
    make_dict []
  |) in
(* At stmt: unsupported node type: Try *)
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      M.get_name (| globals, "kzg_proof_verification" |);
      M.get_name (| globals, "KZGProofError" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      M.call (|
        M.get_name (| globals, "Bytes" |),
        make_list [
          BinOp.add (|
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  M.get_name (| globals, "FIELD_ELEMENTS_PER_BLOB" |)
                ],
                make_dict []
              |), "to_be_bytes32" |),
              make_list [],
              make_dict []
            |),
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  M.get_name (| globals, "BLS_MODULUS" |)
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
