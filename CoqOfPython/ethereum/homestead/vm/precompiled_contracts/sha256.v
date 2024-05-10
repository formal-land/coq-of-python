Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) SHA256 PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the `SHA256` precompiled contract.
".

(* At top_level_stmt: unsupported node type: Import *)

Require ethereum.base_types.
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.utils.numeric.
Axiom ethereum_utils_numeric_ceil32 :
  IsGlobalAlias globals ethereum.utils.numeric.globals "ceil32".

Require ethereum.homestead.vm.__init__.
Axiom ethereum_homestead_vm___init___Evm :
  IsGlobalAlias globals ethereum.homestead.vm.__init__.globals "Evm".

Require ethereum.homestead.vm.gas.
Axiom ethereum_homestead_vm_gas_GAS_SHA256 :
  IsGlobalAlias globals ethereum.homestead.vm.gas.globals "GAS_SHA256".
Axiom ethereum_homestead_vm_gas_GAS_SHA256_WORD :
  IsGlobalAlias globals ethereum.homestead.vm.gas.globals "GAS_SHA256_WORD".
Axiom ethereum_homestead_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.homestead.vm.gas.globals "charge_gas".

Definition sha256 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Writes the sha256 hash to output.

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
        M.get_name (| globals, "GAS_SHA256" |),
        BinOp.mult (|
          M.get_name (| globals, "GAS_SHA256_WORD" |),
          M.get_name (| globals, "word_count" |)
        |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      M.call (|
        M.get_field (| M.call (|
          M.get_field (| M.get_name (| globals, "hashlib" |), "sha256" |),
          make_list [
            M.get_name (| globals, "data" |)
          ],
          make_dict []
        |), "digest" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
