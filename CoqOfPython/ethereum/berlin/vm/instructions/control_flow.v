Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Control Flow Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM control flow instructions.
".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.berlin.vm.gas.
Axiom ethereum_berlin_vm_gas_GAS_BASE :
  IsGlobalAlias globals ethereum.berlin.vm.gas.globals "GAS_BASE".
Axiom ethereum_berlin_vm_gas_GAS_HIGH :
  IsGlobalAlias globals ethereum.berlin.vm.gas.globals "GAS_HIGH".
Axiom ethereum_berlin_vm_gas_GAS_JUMPDEST :
  IsGlobalAlias globals ethereum.berlin.vm.gas.globals "GAS_JUMPDEST".
Axiom ethereum_berlin_vm_gas_GAS_MID :
  IsGlobalAlias globals ethereum.berlin.vm.gas.globals "GAS_MID".
Axiom ethereum_berlin_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.berlin.vm.gas.globals "charge_gas".

Require ethereum.berlin.vm.__init__.
Axiom ethereum_berlin_vm___init___Evm :
  IsGlobalAlias globals ethereum.berlin.vm.__init__.globals "Evm".

Require ethereum.berlin.vm.exceptions.
Axiom ethereum_berlin_vm_exceptions_InvalidJumpDestError :
  IsGlobalAlias globals ethereum.berlin.vm.exceptions.globals "InvalidJumpDestError".

Require ethereum.berlin.vm.stack.
Axiom ethereum_berlin_vm_stack_pop :
  IsGlobalAlias globals ethereum.berlin.vm.stack.globals "pop".
Axiom ethereum_berlin_vm_stack_push :
  IsGlobalAlias globals ethereum.berlin.vm.stack.globals "push".

Definition stop : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Stop further execution of EVM code.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.pass (| |) in
    let _ := M.pass (| |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "running" |),
      Constant.bool false
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition jump : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Alter the program counter to the location specified by the top of the
    stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let jump_dest :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_MID" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_in (|
          M.get_name (| globals, "jump_dest" |),
          M.get_field (| M.get_name (| globals, "evm" |), "valid_jump_destinations" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some(M.get_name (| globals, "InvalidJumpDestError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.get_name (| globals, "jump_dest" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition jumpi : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Alter the program counter to the specified location if and only if a
    condition is true. If the condition is not true, then the program counter
    would increase only by 1.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let jump_dest :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let conditional_value :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_HIGH" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "conditional_value" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let destination :=
          BinOp.add (|
            M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
            Constant.int 1
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.not_in (|
              M.get_name (| globals, "jump_dest" |),
              M.get_field (| M.get_name (| globals, "evm" |), "valid_jump_destinations" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some(M.get_name (| globals, "InvalidJumpDestError" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let destination :=
              M.get_name (| globals, "jump_dest" |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.get_name (| globals, "destination" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition pc : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push onto the stack the value of the program counter after reaching the
    current instruction and without increasing it for the next instruction.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_BASE" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "pc" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition gas_left : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push the amount of available gas (including the corresponding reduction
    for the cost of this instruction) onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_BASE" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition jumpdest : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Mark a valid destination for jumps. This is a noop, present only
    to be used by `JUMP` and `JUMPI` opcodes to verify that their jump is
    valid.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_JUMPDEST" |)
    ],
    make_dict []
  |) in
    let _ := M.pass (| |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).
