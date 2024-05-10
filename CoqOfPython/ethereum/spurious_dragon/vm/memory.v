Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.spurious_dragon.vm.memory".

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

Axiom ethereum_utils_byte_imports :
  AreImported globals "ethereum.utils.byte" [ "right_pad_zero_bytes" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U256"; "Bytes"; "Uint" ].

Definition memory_write : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "memory"; "start_position"; "value" ] |) in
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
        M.get_name (| globals, "memory" |),
        M.get_name (| globals, "start_position" |),
        BinOp.add (|
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "start_position" |)
            ],
            make_dict []
          |),
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "value" |)
            ],
            make_dict []
          |)
        |),
        Constant.None_
      |),
      M.get_name (| globals, "value" |)
    |) in
    M.pure Constant.None_)).

Definition memory_read_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "memory"; "start_position"; "size" ] |) in
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
        M.get_name (| globals, "memory" |),
        M.get_name (| globals, "start_position" |),
        BinOp.add (|
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "start_position" |)
            ],
            make_dict []
          |),
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "size" |)
            ],
            make_dict []
          |)
        |),
        Constant.None_
      |)
    |) in
    M.pure Constant.None_)).

Definition buffer_read : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "buffer"; "start_position"; "size" ] |) in
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
        M.get_name (| globals, "right_pad_zero_bytes" |),
        make_list [
          M.slice (|
            M.get_name (| globals, "buffer" |),
            M.get_name (| globals, "start_position" |),
            BinOp.add (|
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  M.get_name (| globals, "start_position" |)
                ],
                make_dict []
              |),
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  M.get_name (| globals, "size" |)
                ],
                make_dict []
              |)
            |),
            Constant.None_
          |);
          M.get_name (| globals, "size" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
