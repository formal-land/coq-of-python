Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.frontier.vm.instructions.stack".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Stack Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM stack related instructions.
".

Axiom functools_imports_partial :
  IsImported globals "functools" "partial".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".

Axiom ethereum_utils_ensure_imports_ensure :
  IsImported globals "ethereum.utils.ensure" "ensure".

Axiom ethereum_frontier_vm_imports_Evm :
  IsImported globals "ethereum.frontier.vm" "Evm".
Axiom ethereum_frontier_vm_imports_stack :
  IsImported globals "ethereum.frontier.vm" "stack".

Axiom ethereum_frontier_vm_exceptions_imports_StackUnderflowError :
  IsImported globals "ethereum.frontier.vm.exceptions" "StackUnderflowError".

Axiom ethereum_frontier_vm_gas_imports_GAS_BASE :
  IsImported globals "ethereum.frontier.vm.gas" "GAS_BASE".
Axiom ethereum_frontier_vm_gas_imports_GAS_VERY_LOW :
  IsImported globals "ethereum.frontier.vm.gas" "GAS_VERY_LOW".
Axiom ethereum_frontier_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.frontier.vm.gas" "charge_gas".

Axiom ethereum_frontier_vm_memory_imports_buffer_read :
  IsImported globals "ethereum.frontier.vm.memory" "buffer_read".

Definition pop : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Remove item from stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "stack" |), "pop" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BASE" |)
    ],
    make_dict []
  |) in
    let _ := M.pass (| |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition push_n : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm"; "num_bytes" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Pushes a N-byte immediate onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    num_bytes :
        The number of immediate bytes to be read from the code and pushed to
        the stack.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "data_to_push" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "code" |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  BinOp.add (|
                    M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
                    Constant.int 1
                  |)
                ],
                make_dict []
              |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  M.get_name (| globals, locals_stack, "num_bytes" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "stack" |), "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "data_to_push" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      BinOp.add (|
    Constant.int 1,
    M.get_name (| globals, locals_stack, "num_bytes" |)
  |)
    |) in
    M.pure Constant.None_)).

Definition dup_n : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm"; "item_number" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Duplicate the Nth stack item (from top of the stack) to the top of stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    item_number :
        The stack item number (0-indexed from top of stack) to be duplicated
        to the top of stack.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "ensure" |),
    make_list [
      Compare.lt (|
        M.get_name (| globals, locals_stack, "item_number" |),
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, locals_stack, "StackUnderflowError" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "data_to_duplicate" ,
      M.get_subscript (|
        M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |),
        BinOp.sub (|
          BinOp.sub (|
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
              ],
              make_dict []
            |),
            Constant.int 1
          |),
          M.get_name (| globals, locals_stack, "item_number" |)
        |)
      |)
    |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "stack" |), "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "data_to_duplicate" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition swap_n : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm"; "item_number" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Swap the top and the `item_number` element of the stack, where
    the top of the stack is position zero.

    If `item_number` is zero, this function does nothing (which should not be
    possible, since there is no `SWAP0` instruction).

    Parameters
    ----------
    evm :
        The current EVM frame.

    item_number :
        The stack item number (0-indexed from top of stack) to be swapped
        with the top of stack element.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "ensure" |),
    make_list [
      Compare.lt (|
        M.get_name (| globals, locals_stack, "item_number" |),
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, locals_stack, "StackUnderflowError" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      make_tuple [ M.get_subscript (|
        M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |),
        UnOp.sub (| Constant.int 1 |)
      |); M.get_subscript (|
        M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |),
        BinOp.sub (|
          UnOp.sub (| Constant.int 1 |),
          M.get_name (| globals, locals_stack, "item_number" |)
        |)
      |) ],
      make_tuple [ M.get_subscript (|
        M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |),
        BinOp.sub (|
          UnOp.sub (| Constant.int 1 |),
          M.get_name (| globals, locals_stack, "item_number" |)
        |)
      |); M.get_subscript (|
        M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |),
        UnOp.sub (| Constant.int 1 |)
      |) ]
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition push1 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push2 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push3 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push4 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push5 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push6 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push7 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push8 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push9 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push10 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push11 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push12 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push13 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push14 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push15 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push16 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push17 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push18 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push19 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push20 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push21 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push22 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push23 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push24 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push25 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push26 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push27 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push28 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push29 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push30 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push31 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push32 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition dup1 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup2 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup3 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup4 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup5 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup6 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup7 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup8 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup9 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup10 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup11 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup12 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup13 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup14 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup15 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup16 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition swap1 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap2 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap3 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap4 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap5 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap6 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap7 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap8 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap9 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap10 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap11 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap12 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap13 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap14 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap15 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap16 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "swap_n" |)
    ],
    make_dict []
  |)
)).
