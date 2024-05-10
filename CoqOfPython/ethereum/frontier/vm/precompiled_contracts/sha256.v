Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.frontier.vm.precompiled_contracts.sha256".

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

Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_utils_numeric_imports_ceil32 :
  IsImported globals "ethereum.utils.numeric" "ceil32".

Axiom ethereum_frontier_vm_imports_Evm :
  IsImported globals "ethereum.frontier.vm" "Evm".

Axiom ethereum_frontier_vm_gas_imports_GAS_SHA256 :
  IsImported globals "ethereum.frontier.vm.gas" "GAS_SHA256".
Axiom ethereum_frontier_vm_gas_imports_GAS_SHA256_WORD :
  IsImported globals "ethereum.frontier.vm.gas" "GAS_SHA256_WORD".
Axiom ethereum_frontier_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.frontier.vm.gas" "charge_gas".

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
