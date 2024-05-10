Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require ethereum.base_types.
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.utils.byte.
Axiom ethereum_utils_byte_left_pad_zero_bytes :
  IsGlobalAlias globals ethereum.utils.byte.globals "left_pad_zero_bytes".

Require ethereum.utils.numeric.
Axiom ethereum_utils_numeric_ceil32 :
  IsGlobalAlias globals ethereum.utils.numeric.globals "ceil32".

Require ethereum.tangerine_whistle.vm.__init__.
Axiom ethereum_tangerine_whistle_vm___init___Evm :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.__init__.globals "Evm".

Require ethereum.tangerine_whistle.vm.gas.
Axiom ethereum_tangerine_whistle_vm_gas_GAS_RIPEMD160 :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.gas.globals "GAS_RIPEMD160".
Axiom ethereum_tangerine_whistle_vm_gas_GAS_RIPEMD160_WORD :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.gas.globals "GAS_RIPEMD160_WORD".
Axiom ethereum_tangerine_whistle_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.gas.globals "charge_gas".

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
