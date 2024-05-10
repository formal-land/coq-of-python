Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.utils.byte".

Definition expr_1 : Value.t :=
  Constant.str "
Utility Functions For Byte Strings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Byte specific utility functions used in this specification.
".

Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".

Definition left_pad_zero_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "value"; "size" ] |) in
    let _ := Constant.str "
    Left pad zeroes to `value` if it's length is less than the given `size`.

    Parameters
    ----------
    value :
        The byte string that needs to be padded.
    size :
        The number of bytes that need that need to be padded.

    Returns
    -------
    left_padded_value: `ethereum.base_types.Bytes`
        left padded byte string of given `size`.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, "value" |), "rjust" |),
        make_list [
          M.get_name (| globals, "size" |);
          Constant.bytes "00"
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition right_pad_zero_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "value"; "size" ] |) in
    let _ := Constant.str "
    Right pad zeroes to `value` if it's length is less than the given `size`.

    Parameters
    ----------
    value :
        The byte string that needs to be padded.
    size :
        The number of bytes that need that need to be padded.

    Returns
    -------
    right_padded_value: `ethereum.base_types.Bytes`
        right padded byte string of given `size`.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, "value" |), "ljust" |),
        make_list [
          M.get_name (| globals, "size" |);
          Constant.bytes "00"
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
