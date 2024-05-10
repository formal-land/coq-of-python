Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.shanghai.vm.precompiled_contracts.identity".

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

Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_utils_numeric_imports_ceil32 :
  IsImported globals "ethereum.utils.numeric" "ceil32".

Axiom ethereum_shanghai_vm_imports_Evm :
  IsImported globals "ethereum.shanghai.vm" "Evm".

Axiom ethereum_shanghai_vm_gas_imports_GAS_IDENTITY :
  IsImported globals "ethereum.shanghai.vm.gas" "GAS_IDENTITY".
Axiom ethereum_shanghai_vm_gas_imports_GAS_IDENTITY_WORD :
  IsImported globals "ethereum.shanghai.vm.gas" "GAS_IDENTITY_WORD".
Axiom ethereum_shanghai_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.shanghai.vm.gas" "charge_gas".

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
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.assign_local (|
      "word_count" ,
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
      |)
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
