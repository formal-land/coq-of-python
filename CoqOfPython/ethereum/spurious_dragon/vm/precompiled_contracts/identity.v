Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) IDENTITY PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the `IDENTITY` precompiled contract.
".

Require ethereum.base_types.
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.utils.numeric.
Axiom ethereum_utils_numeric_ceil32 :
  IsGlobalAlias globals ethereum.utils.numeric.globals "ceil32".

Require ethereum.spurious_dragon.vm.__init__.
Axiom ethereum_spurious_dragon_vm___init___Evm :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.__init__.globals "Evm".

Require ethereum.spurious_dragon.vm.gas.
Axiom ethereum_spurious_dragon_vm_gas_GAS_IDENTITY :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.gas.globals "GAS_IDENTITY".
Axiom ethereum_spurious_dragon_vm_gas_GAS_IDENTITY_WORD :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.gas.globals "GAS_IDENTITY_WORD".
Axiom ethereum_spurious_dragon_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.gas.globals "charge_gas".

Definition identity : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Writes the message data to output.

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
        M.get_name (| globals, "GAS_IDENTITY" |),
        BinOp.mult (|
          M.get_name (| globals, "GAS_IDENTITY_WORD" |),
          M.get_name (| globals, "word_count" |)
        |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      M.get_name (| globals, "data" |)
    |) in
    M.pure Constant.None_)).
