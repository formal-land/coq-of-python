Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require ethereum.utils.byte.
Axiom ethereum_utils_byte_right_pad_zero_bytes :
  IsGlobalAlias globals ethereum.utils.byte.globals "right_pad_zero_bytes".

Require base_types.
Axiom base_types_U256 :
  IsGlobalAlias globals base_types.globals "U256".
Axiom base_types_Bytes :
  IsGlobalAlias globals base_types.globals "Bytes".
Axiom base_types_Uint :
  IsGlobalAlias globals base_types.globals "Uint".

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
      M.get_subscript (| M.get_name (| globals, "memory" |), M.get_name (| globals, "start_position" |) |),
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
      M.get_subscript (| M.get_name (| globals, "memory" |), M.get_name (| globals, "start_position" |) |)
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
          M.get_subscript (| M.get_name (| globals, "buffer" |), M.get_name (| globals, "start_position" |) |);
          M.get_name (| globals, "size" |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).
