Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.spurious_dragon.vm.precompiled_contracts.sha256".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_spurious_dragon_vm_imports_Evm :
  IsImported globals "ethereum.spurious_dragon.vm" "Evm".

Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_SHA256 :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_SHA256".
Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_SHA256_WORD :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_SHA256_WORD".
Axiom ethereum_spurious_dragon_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "charge_gas".

Definition sha256 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Writes the sha256 hash to output.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.assign_local (|
      "word_count" ,
      BinOp.floor_div (|
        M.call (|
          M.get_name (| globals, locals_stack, "ceil32" |),
          make_list [
            M.call (|
              M.get_name (| globals, locals_stack, "Uint" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "data" |)
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
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.add (|
        M.get_name (| globals, locals_stack, "GAS_SHA256" |),
        BinOp.mult (|
          M.get_name (| globals, locals_stack, "GAS_SHA256_WORD" |),
          M.get_name (| globals, locals_stack, "word_count" |)
        |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
      M.call (|
        M.get_field (| M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "hashlib" |), "sha256" |),
          make_list [
            M.get_name (| globals, locals_stack, "data" |)
          ],
          make_dict []
        |), "digest" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom sha256_in_globals :
  IsInGlobals globals "sha256" (make_function sha256).
