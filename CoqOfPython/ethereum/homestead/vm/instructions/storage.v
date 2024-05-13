Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.homestead.vm.instructions.storage".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Storage Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM storage related instructions.
".

Axiom ethereum_homestead_state_imports_get_storage :
  IsImported globals "ethereum.homestead.state" "get_storage".
Axiom ethereum_homestead_state_imports_set_storage :
  IsImported globals "ethereum.homestead.state" "set_storage".

Axiom ethereum_homestead_vm_imports_Evm :
  IsImported globals "ethereum.homestead.vm" "Evm".

Axiom ethereum_homestead_vm_gas_imports_GAS_SLOAD :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_SLOAD".
Axiom ethereum_homestead_vm_gas_imports_GAS_STORAGE_CLEAR_REFUND :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_STORAGE_CLEAR_REFUND".
Axiom ethereum_homestead_vm_gas_imports_GAS_STORAGE_SET :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_STORAGE_SET".
Axiom ethereum_homestead_vm_gas_imports_GAS_STORAGE_UPDATE :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_STORAGE_UPDATE".
Axiom ethereum_homestead_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.homestead.vm.gas" "charge_gas".

Axiom ethereum_homestead_vm_stack_imports_pop :
  IsImported globals "ethereum.homestead.vm.stack" "pop".
Axiom ethereum_homestead_vm_stack_imports_push :
  IsImported globals "ethereum.homestead.vm.stack" "push".

Definition sload : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Loads to the stack, the value corresponding to a certain key from the
    storage of the current account.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "key" ,
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_SLOAD" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, locals_stack, "key" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom sload_in_globals :
  IsInGlobals globals "sload" (make_function sload).

Definition sstore : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Stores a value at a certain key in the current context's storage.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "key" ,
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "new_value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "current_value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, locals_stack, "key" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.not_eq (|
            M.get_name (| globals, locals_stack, "new_value" |),
            Constant.int 0
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_name (| globals, locals_stack, "current_value" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "gas_cost" ,
          M.get_name (| globals, locals_stack, "GAS_STORAGE_SET" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "gas_cost" ,
          M.get_name (| globals, locals_stack, "GAS_STORAGE_UPDATE" |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.eq (|
            M.get_name (| globals, locals_stack, "new_value" |),
            Constant.int 0
          |),
          ltac:(M.monadic (
            Compare.not_eq (|
              M.get_name (| globals, locals_stack, "current_value" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "refund_counter" |),
          M.get_name (| globals, locals_stack, "GAS_STORAGE_CLEAR_REFUND" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "gas_cost" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_storage" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, locals_stack, "key" |);
      M.get_name (| globals, locals_stack, "new_value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom sstore_in_globals :
  IsInGlobals globals "sstore" (make_function sstore).
