Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.london.vm.memory".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Memory
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

EVM memory operations.
".

Axiom ethereum_utils_byte_imports_right_pad_zero_bytes :
  IsImported globals "ethereum.utils.byte" "right_pad_zero_bytes".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Definition memory_write : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "memory"; "start_position"; "value" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Writes to memory.

    Parameters
    ----------
    memory :
        Memory contents of the EVM.
    start_position :
        Starting pointer to the memory.
    value :
        Data to write to memory.
    " in
    let _ := M.assign (|
      M.slice (|
        M.get_name (| globals, locals_stack, "memory" |),
        M.get_name (| globals, locals_stack, "start_position" |),
        BinOp.add (|
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_name (| globals, locals_stack, "start_position" |)
            ],
            make_dict []
          |),
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "value" |)
            ],
            make_dict []
          |)
        |),
        Constant.None_
      |),
      M.get_name (| globals, locals_stack, "value" |)
    |) in
    M.pure Constant.None_)).

Definition memory_read_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "memory"; "start_position"; "size" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Read bytes from memory.

    Parameters
    ----------
    memory :
        Memory contents of the EVM.
    start_position :
        Starting pointer to the memory.
    size :
        Size of the data that needs to be read from `start_position`.

    Returns
    -------
    data_bytes :
        Data read from memory.
    " in
    let _ := M.return_ (|
      M.slice (|
        M.get_name (| globals, locals_stack, "memory" |),
        M.get_name (| globals, locals_stack, "start_position" |),
        BinOp.add (|
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_name (| globals, locals_stack, "start_position" |)
            ],
            make_dict []
          |),
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_name (| globals, locals_stack, "size" |)
            ],
            make_dict []
          |)
        |),
        Constant.None_
      |)
    |) in
    M.pure Constant.None_)).

Definition buffer_read : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "buffer"; "start_position"; "size" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Read bytes from a buffer. Padding with zeros if necessary.

    Parameters
    ----------
    buffer :
        Memory contents of the EVM.
    start_position :
        Starting pointer to the memory.
    size :
        Size of the data that needs to be read from `start_position`.

    Returns
    -------
    data_bytes :
        Data read from memory.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "right_pad_zero_bytes" |),
        make_list [
          M.slice (|
            M.get_name (| globals, locals_stack, "buffer" |),
            M.get_name (| globals, locals_stack, "start_position" |),
            BinOp.add (|
              M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  M.get_name (| globals, locals_stack, "start_position" |)
                ],
                make_dict []
              |),
              M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  M.get_name (| globals, locals_stack, "size" |)
                ],
                make_dict []
              |)
            |),
            Constant.None_
          |);
          M.get_name (| globals, locals_stack, "size" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
