Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.arrow_glacier.vm.precompiled_contracts.blake2f".

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

Axiom ethereum_utils_ensure_imports_ensure :
  IsImported globals "ethereum.utils.ensure" "ensure".

Axiom ethereum_arrow_glacier_vm_imports_Evm :
  IsImported globals "ethereum.arrow_glacier.vm" "Evm".

Axiom ethereum_arrow_glacier_vm_gas_imports_GAS_BLAKE2_PER_ROUND :
  IsImported globals "ethereum.arrow_glacier.vm.gas" "GAS_BLAKE2_PER_ROUND".
Axiom ethereum_arrow_glacier_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.arrow_glacier.vm.gas" "charge_gas".

Axiom ethereum_arrow_glacier_vm_exceptions_imports_InvalidParameter :
  IsImported globals "ethereum.arrow_glacier.vm.exceptions" "InvalidParameter".

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
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_name (| globals, locals_stack, "data" |)
          ],
          make_dict []
        |),
        Constant.int 213
      |);
      M.get_name (| globals, locals_stack, "InvalidParameter" |)
    ],
    make_dict []
  |) in
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
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "ensure" |),
    make_list [
      Compare.in_ (|
        M.get_name (| globals, locals_stack, "f" |),
        make_list [
          Constant.int 0;
          Constant.int 1
        ]
      |);
      M.get_name (| globals, locals_stack, "InvalidParameter" |)
    ],
    make_dict []
  |) in
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
