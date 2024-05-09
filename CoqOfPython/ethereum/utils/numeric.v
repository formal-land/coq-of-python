Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Utility Functions For Numeric Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Numeric operations specific utility functions used in this specification.
".

Require typing.
Axiom typing_Sequence :
  IsGlobalAlias globals typing.globals "Sequence".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".

Require ethereum.base_types.
Axiom ethereum_base_types_U32 :
  IsGlobalAlias globals ethereum.base_types.globals "U32".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Definition get_sign : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "value" ] |) in
    let _ := Constant.str "
    Determines the sign of a number.

    Parameters
    ----------
    value :
        The value whose sign is to be determined.

    Returns
    -------
    sign : `int`
        The sign of the number (-1 or 0 or 1).
        The return value is based on math signum function.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (| M.get_name (| globals, "value" |), Constant.int 0 |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          UnOp.sub (| Constant.int 1 |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (| M.get_name (| globals, "value" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              Constant.int 0
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.return_ (|
              Constant.int 1
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition ceil32 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "value" ] |) in
    let _ := Constant.str "
    Converts a unsigned integer to the next closest multiple of 32.

    Parameters
    ----------
    value :
        The value whose ceil32 is to be calculated.

    Returns
    -------
    ceil32 : `ethereum.base_types.U256`
        The same value if it's a perfect multiple of 32
        else it returns the smallest multiple of 32
        that is greater than `value`.
    " in
    let ceiling :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 32
        ],
        make_dict []
      |) in
    let remainder :=
      BinOp.mod_ (|
        M.get_name (| globals, "value" |),
        M.get_name (| globals, "ceiling" |)
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (| M.get_name (| globals, "remainder" |), M.call (|
          M.get_name (| globals, "Uint" |),
          make_list [
            Constant.int 0
          ],
          make_dict []
        |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, "value" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          BinOp.sub (|
            BinOp.add (|
              M.get_name (| globals, "value" |),
              M.get_name (| globals, "ceiling" |)
            |),
            M.get_name (| globals, "remainder" |)
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition is_prime : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "number" ] |) in
    let _ := Constant.str "
    Checks if `number` is a prime number.

    Parameters
    ----------
    number :
        The number to check for primality.

    Returns
    -------
    is_number_prime : `bool`
        Boolean indicating if `number` is prime or not.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (| M.get_name (| globals, "number" |), Constant.int 1 |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.bool false
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    For M.get_name (| globals, "x" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      Constant.int 2;
      BinOp.add (|
        M.call (|
          M.get_name (| globals, "int" |),
          make_list [
            BinOp.pow (|
              M.get_name (| globals, "number" |),
              Value.Float 0.5
            |)
          ],
          make_dict []
        |),
        Constant.int 1
      |)
    ],
    make_dict []
  |) do
      let _ :=
        (* if *)
        M.if_then_else (|
          Compare.eq (| BinOp.mod_ (|
            M.get_name (| globals, "number" |),
            M.get_name (| globals, "x" |)
          |), Constant.int 0 |),
        (* then *)
        ltac:(M.monadic (
          let _ := M.return_ (|
            Constant.bool false
          |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          M.pure Constant.None_
        )) |) in
    EndFor.
    let _ := M.return_ (|
      Constant.bool true
    |) in
    M.pure Constant.None_)).

Definition le_bytes_to_uint32_sequence : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "data" ] |) in
    let _ := Constant.str "
    Convert little endian byte stream `data` to a little endian U32
    sequence i.e., the first U32 number of the sequence is the least
    significant U32 number.

    Parameters
    ----------
    data :
        The byte stream (little endian) which is to be converted to a U32
        stream.

    Returns
    -------
    uint32_sequence : `Tuple[U32, ...]`
        Sequence of U32 numbers obtained from the little endian byte
        stream.
    " in
    let sequence :=
      make_list [] in
    For M.get_name (| globals, "i" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      Constant.int 0;
      M.call (|
        M.get_name (| globals, "len" |),
        make_list [
          M.get_name (| globals, "data" |)
        ],
        make_dict []
      |);
      Constant.int 4
    ],
    make_dict []
  |) do
      let _ := M.call (|
    M.get_field (| M.get_name (| globals, "sequence" |), "append" |),
    make_list [
      M.call (|
        M.get_field (| M.get_name (| globals, "U32" |), "from_le_bytes" |),
        make_list [
          M.get_subscript (| M.get_name (| globals, "data" |), M.get_name (| globals, "i" |):BinOp.add (|
            M.get_name (| globals, "i" |),
            Constant.int 4
          |) |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    EndFor.
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "tuple" |),
        make_list [
          M.get_name (| globals, "sequence" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition le_uint32_sequence_to_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "sequence" ] |) in
    let _ := Constant.str "
    Obtain little endian byte stream from a little endian U32 sequence
    i.e., the first U32 number of the sequence is the least significant
    U32 number.

    Note - In this conversion, the most significant byte (byte at the end of
    the little endian stream) may have leading zeroes. This function doesn't
    take care of removing these leading zeroes as shown in below example.

    >>> le_uint32_sequence_to_bytes([U32(8)])
    b'\x08\x00\x00\x00'


    Parameters
    ----------
    sequence :
        The U32 stream (little endian) which is to be converted to a
        little endian byte stream.

    Returns
    -------
    result : `bytes`
        The byte stream obtained from the little endian U32 stream.
    " in
    let result_bytes :=
      (* At constant: unsupported node type: Constant *) in
    For M.get_name (| globals, "item" |) in M.get_name (| globals, "sequence" |) do
      let result_bytes := BinOp.add
        M.call (|
    M.get_field (| M.get_name (| globals, "item" |), "to_le_bytes4" |),
    make_list [],
    make_dict []
  |)
        M.call (|
    M.get_field (| M.get_name (| globals, "item" |), "to_le_bytes4" |),
    make_list [],
    make_dict []
  |) in
    EndFor.
    let _ := M.return_ (|
      M.get_name (| globals, "result_bytes" |)
    |) in
    M.pure Constant.None_)).

Definition le_uint32_sequence_to_uint : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "sequence" ] |) in
    let _ := Constant.str "
    Obtain Uint from a U32 sequence assuming that this sequence is little
    endian i.e., the first U32 number of the sequence is the least
    significant U32 number.

    Parameters
    ----------
    sequence :
        The U32 stream (little endian) which is to be converted to a Uint.

    Returns
    -------
    value : `Uint`
        The Uint number obtained from the conversion of the little endian
        U32 stream.
    " in
    let sequence_as_bytes :=
      M.call (|
        M.get_name (| globals, "le_uint32_sequence_to_bytes" |),
        make_list [
          M.get_name (| globals, "sequence" |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, "Uint" |), "from_le_bytes" |),
        make_list [
          M.get_name (| globals, "sequence_as_bytes" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition taylor_exponential : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "factor"; "numerator"; "denominator" ] |) in
    let _ := Constant.str "
    Approximates factor * e ** (numerator / denominator) using
    Taylor expansion.

    Parameters
    ----------
    factor :
        The factor.
    numerator :
        The numerator of the exponential.
    denominator :
        The denominator of the exponential.

    Returns
    -------
    output : `ethereum.base_types.Uint`
        The approximation of factor * e ** (numerator / denominator).

    " in
    let i :=
      Constant.int 1 in
    let output :=
      Constant.int 0 in
    let numerator_accumulated :=
      BinOp.mult (|
        M.get_name (| globals, "factor" |),
        M.get_name (| globals, "denominator" |)
      |) in
    While Compare.gt (| M.get_name (| globals, "numerator_accumulated" |), Constant.int 0 |) do
      let output := BinOp.add
        M.get_name (| globals, "numerator_accumulated" |)
        M.get_name (| globals, "numerator_accumulated" |) in
      let numerator_accumulated :=
        BinOp.floor_div (|
          BinOp.mult (|
            M.get_name (| globals, "numerator_accumulated" |),
            M.get_name (| globals, "numerator" |)
          |),
          BinOp.mult (|
            M.get_name (| globals, "denominator" |),
            M.get_name (| globals, "i" |)
          |)
        |) in
      let i := BinOp.add
        Constant.int 1
        Constant.int 1 in
    EndWhile.
    let _ := M.return_ (|
      BinOp.floor_div (|
        M.get_name (| globals, "output" |),
        M.get_name (| globals, "denominator" |)
      |)
    |) in
    M.pure Constant.None_)).
