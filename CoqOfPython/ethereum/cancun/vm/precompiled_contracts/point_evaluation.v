Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.cancun.vm.precompiled_contracts.point_evaluation".

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

Axiom eth2spec_deneb_mainnet_imports :
  AreImported globals "eth2spec.deneb.mainnet" [ "KZGCommitment"; "kzg_commitment_to_versioned_hash"; "verify_kzg_proof" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U256"; "Bytes" ].

Axiom ethereum_utils_ensure_imports :
  AreImported globals "ethereum.utils.ensure" [ "ensure" ].

Axiom ethereum_cancun_vm_imports :
  AreImported globals "ethereum.cancun.vm" [ "Evm" ].

Axiom ethereum_cancun_vm_exceptions_imports :
  AreImported globals "ethereum.cancun.vm.exceptions" [ "KZGProofError" ].

Axiom ethereum_cancun_vm_gas_imports :
  AreImported globals "ethereum.cancun.vm.gas" [ "GAS_POINT_EVALUATION"; "charge_gas" ].

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
      M.slice (|
        M.get_name (| globals, "data" |),
        Constant.None_,
        Constant.int 32,
        Constant.None_
      |) in
    let z :=
      M.slice (|
        M.get_name (| globals, "data" |),
        Constant.int 32,
        Constant.int 64,
        Constant.None_
      |) in
    let y :=
      M.slice (|
        M.get_name (| globals, "data" |),
        Constant.int 64,
        Constant.int 96,
        Constant.None_
      |) in
    let commitment :=
      M.call (|
        M.get_name (| globals, "KZGCommitment" |),
        make_list [
          M.slice (|
            M.get_name (| globals, "data" |),
            Constant.int 96,
            Constant.int 144,
            Constant.None_
          |)
        ],
        make_dict []
      |) in
    let proof :=
      M.slice (|
        M.get_name (| globals, "data" |),
        Constant.int 144,
        Constant.int 192,
        Constant.None_
      |) in
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
