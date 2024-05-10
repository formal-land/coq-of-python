Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require functools.
Axiom functools_partial :
  IsGlobalAlias globals functools.globals "partial".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require ethereum.muir_glacier.vm.__init__.
Axiom ethereum_muir_glacier_vm___init___Evm :
  IsGlobalAlias globals ethereum.muir_glacier.vm.__init__.globals "Evm".
Axiom ethereum_muir_glacier_vm___init___stack :
  IsGlobalAlias globals ethereum.muir_glacier.vm.__init__.globals "stack".

Require ethereum.muir_glacier.vm.exceptions.
Axiom ethereum_muir_glacier_vm_exceptions_StackUnderflowError :
  IsGlobalAlias globals ethereum.muir_glacier.vm.exceptions.globals "StackUnderflowError".

Require ethereum.muir_glacier.vm.gas.
Axiom ethereum_muir_glacier_vm_gas_GAS_BASE :
  IsGlobalAlias globals ethereum.muir_glacier.vm.gas.globals "GAS_BASE".
Axiom ethereum_muir_glacier_vm_gas_GAS_VERY_LOW :
  IsGlobalAlias globals ethereum.muir_glacier.vm.gas.globals "GAS_VERY_LOW".
Axiom ethereum_muir_glacier_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.muir_glacier.vm.gas.globals "charge_gas".

Require ethereum.muir_glacier.vm.memory.
Axiom ethereum_muir_glacier_vm_memory_buffer_read :
  IsGlobalAlias globals ethereum.muir_glacier.vm.memory.globals "buffer_read".

Definition pop : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Remove item from stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, "stack" |), "pop" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_BASE" |)
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

Definition push_n : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "num_bytes" ] |) in
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
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let data_to_push :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "code" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  BinOp.add (|
                    M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
                    Constant.int 1
                  |)
                ],
                make_dict []
              |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  M.get_name (| globals, "num_bytes" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, "stack" |), "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "data_to_push" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      BinOp.add (|
    Constant.int 1,
    M.get_name (| globals, "num_bytes" |)
  |)
    |) in
    M.pure Constant.None_)).

Definition dup_n : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "item_number" ] |) in
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
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt (|
        M.get_name (| globals, "item_number" |),
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, "StackUnderflowError" |)
    ],
    make_dict []
  |) in
    let data_to_duplicate :=
      M.get_subscript (| M.get_field (| M.get_name (| globals, "evm" |), "stack" |), BinOp.sub (|
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |),
          Constant.int 1
        |),
        M.get_name (| globals, "item_number" |)
      |) |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, "stack" |), "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "data_to_duplicate" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition swap_n : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "item_number" ] |) in
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
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt (|
        M.get_name (| globals, "item_number" |),
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, "StackUnderflowError" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      make_tuple [ M.get_subscript (| M.get_field (| M.get_name (| globals, "evm" |), "stack" |), UnOp.sub (| Constant.int 1 |) |); M.get_subscript (| M.get_field (| M.get_name (| globals, "evm" |), "stack" |), BinOp.sub (|
        UnOp.sub (| Constant.int 1 |),
        M.get_name (| globals, "item_number" |)
      |) |) ],
      make_tuple [ M.get_subscript (| M.get_field (| M.get_name (| globals, "evm" |), "stack" |), BinOp.sub (|
        UnOp.sub (| Constant.int 1 |),
        M.get_name (| globals, "item_number" |)
      |) |); M.get_subscript (| M.get_field (| M.get_name (| globals, "evm" |), "stack" |), UnOp.sub (| Constant.int 1 |) |) ]
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition push1 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push2 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push3 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push4 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push5 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push6 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push7 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push8 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push9 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push10 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push11 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push12 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push13 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push14 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push15 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push16 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push17 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push18 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push19 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push20 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push21 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push22 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push23 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push24 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push25 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push26 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push27 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push28 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push29 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push30 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push31 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition push32 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "push_n" |)
    ],
    make_dict []
  |)
)).

Definition dup1 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup2 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup3 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup4 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup5 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup6 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup7 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup8 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup9 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup10 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup11 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup12 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup13 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup14 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup15 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition dup16 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "dup_n" |)
    ],
    make_dict []
  |)
)).

Definition swap1 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap2 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap3 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap4 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap5 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap6 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap7 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap8 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap9 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap10 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap11 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap12 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap13 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap14 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap15 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).

Definition swap16 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "swap_n" |)
    ],
    make_dict []
  |)
)).
