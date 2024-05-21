Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.london.vm.precompiled_contracts.blake2f".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Blake2 PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the `Blake2` precompiled contract.
".

Axiom ethereum_crypto_blake2_imports_Blake2b :
  IsImported globals "ethereum.crypto.blake2" "Blake2b".

Axiom ethereum_london_vm_imports_Evm :
  IsImported globals "ethereum.london.vm" "Evm".

Axiom ethereum_london_vm_gas_imports_GAS_BLAKE2_PER_ROUND :
  IsImported globals "ethereum.london.vm.gas" "GAS_BLAKE2_PER_ROUND".
Axiom ethereum_london_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.london.vm.gas" "charge_gas".

Axiom ethereum_london_vm_exceptions_imports_InvalidParameter :
  IsImported globals "ethereum.london.vm.exceptions" "InvalidParameter".

Definition blake2f : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Writes the Blake2 hash to output.

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
          Constant.int 213
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidParameter" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "blake2b" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Blake2b" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      make_tuple [ M.get_name (| globals, locals_stack, "rounds" |); M.get_name (| globals, locals_stack, "h" |); M.get_name (| globals, locals_stack, "m" |); M.get_name (| globals, locals_stack, "t_0" |); M.get_name (| globals, locals_stack, "t_1" |); M.get_name (| globals, locals_stack, "f" |) ],
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "blake2b" |), "get_blake2_parameters" |),
        make_list [
          M.get_name (| globals, locals_stack, "data" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "GAS_BLAKE2_PER_ROUND" |),
        M.get_name (| globals, locals_stack, "rounds" |)
      |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_in (|
          M.get_name (| globals, locals_stack, "f" |),
          make_list [
            Constant.int 0;
            Constant.int 1
          ]
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidParameter" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "blake2b" |), "compress" |),
        make_list [
          M.get_name (| globals, locals_stack, "rounds" |);
          M.get_name (| globals, locals_stack, "h" |);
          M.get_name (| globals, locals_stack, "m" |);
          M.get_name (| globals, locals_stack, "t_0" |);
          M.get_name (| globals, locals_stack, "t_1" |);
          M.get_name (| globals, locals_stack, "f" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom blake2f_in_globals :
  IsInGlobals globals "blake2f" (make_function blake2f).
