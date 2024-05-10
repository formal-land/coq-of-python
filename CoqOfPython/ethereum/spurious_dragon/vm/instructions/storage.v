Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require ethereum.spurious_dragon.state.
Axiom ethereum_spurious_dragon_state_get_storage :
  IsGlobalAlias globals ethereum.spurious_dragon.state.globals "get_storage".
Axiom ethereum_spurious_dragon_state_set_storage :
  IsGlobalAlias globals ethereum.spurious_dragon.state.globals "set_storage".

Require ethereum.spurious_dragon.vm.__init__.
Axiom ethereum_spurious_dragon_vm___init___Evm :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.__init__.globals "Evm".

Require ethereum.spurious_dragon.vm.gas.
Axiom ethereum_spurious_dragon_vm_gas_GAS_SLOAD :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.gas.globals "GAS_SLOAD".
Axiom ethereum_spurious_dragon_vm_gas_GAS_STORAGE_CLEAR_REFUND :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.gas.globals "GAS_STORAGE_CLEAR_REFUND".
Axiom ethereum_spurious_dragon_vm_gas_GAS_STORAGE_SET :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.gas.globals "GAS_STORAGE_SET".
Axiom ethereum_spurious_dragon_vm_gas_GAS_STORAGE_UPDATE :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.gas.globals "GAS_STORAGE_UPDATE".
Axiom ethereum_spurious_dragon_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.gas.globals "charge_gas".

Require ethereum.spurious_dragon.vm.stack.
Axiom ethereum_spurious_dragon_vm_stack_pop :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.stack.globals "pop".
Axiom ethereum_spurious_dragon_vm_stack_push :
  IsGlobalAlias globals ethereum.spurious_dragon.vm.stack.globals "push".

Definition sload : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Loads to the stack, the value corresponding to a certain key from the
    storage of the current account.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let key :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_SLOAD" |)
    ],
    make_dict []
  |) in
    let value :=
      M.call (|
        M.get_name (| globals, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition sstore : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Stores a value at a certain key in the current context's storage.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let key :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |) in
    let new_value :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let current_value :=
      M.call (|
        M.get_name (| globals, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.not_eq (|
            M.get_name (| globals, "new_value" |),
            Constant.int 0
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_name (| globals, "current_value" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let gas_cost :=
          M.get_name (| globals, "GAS_STORAGE_SET" |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let gas_cost :=
          M.get_name (| globals, "GAS_STORAGE_UPDATE" |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.eq (|
            M.get_name (| globals, "new_value" |),
            Constant.int 0
          |),
          ltac:(M.monadic (
            Compare.not_eq (|
              M.get_name (| globals, "current_value" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, "evm" |), "refund_counter" |),
          M.get_name (| globals, "GAS_STORAGE_CLEAR_REFUND" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "gas_cost" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "set_storage" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, "key" |);
      M.get_name (| globals, "new_value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).