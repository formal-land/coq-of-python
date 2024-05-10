Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.istanbul.vm.precompiled_contracts.ripemd160".

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) RIPEMD160 PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the `RIPEMD160` precompiled contract.
".

(* At top_level_stmt: unsupported node type: Import *)

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "Uint" ].

Axiom ethereum_utils_byte_imports :
  AreImported globals "ethereum.utils.byte" [ "left_pad_zero_bytes" ].

Axiom ethereum_utils_numeric_imports :
  AreImported globals "ethereum.utils.numeric" [ "ceil32" ].

Axiom ethereum_istanbul_vm_imports :
  AreImported globals "ethereum.istanbul.vm" [ "Evm" ].

Axiom ethereum_istanbul_vm_gas_imports :
  AreImported globals "ethereum.istanbul.vm.gas" [ "GAS_RIPEMD160"; "GAS_RIPEMD160_WORD"; "charge_gas" ].

Definition ripemd160 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Writes the ripemd160 hash to output.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let data :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |) in
    let word_count :=
      BinOp.floor_div (|
        M.call (|
          M.get_name (| globals, "ceil32" |),
          make_list [
            M.call (|
              M.get_name (| globals, "Uint" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "len" |),
                  make_list [
                    M.get_name (| globals, "data" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          ],
          make_dict []
        |),
        Constant.int 32
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_name (| globals, "GAS_RIPEMD160" |),
        BinOp.mult (|
          M.get_name (| globals, "GAS_RIPEMD160_WORD" |),
          M.get_name (| globals, "word_count" |)
        |)
      |)
    ],
    make_dict []
  |) in
    let hash_bytes :=
      M.call (|
        M.get_field (| M.call (|
          M.get_field (| M.get_name (| globals, "hashlib" |), "new" |),
          make_list [
            Constant.str "ripemd160";
            M.get_name (| globals, "data" |)
          ],
          make_dict []
        |), "digest" |),
        make_list [],
        make_dict []
      |) in
    let padded_hash :=
      M.call (|
        M.get_name (| globals, "left_pad_zero_bytes" |),
        make_list [
          M.get_name (| globals, "hash_bytes" |);
          Constant.int 32
        ],
        make_dict []
      |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      M.get_name (| globals, "padded_hash" |)
    |) in
    M.pure Constant.None_)).
