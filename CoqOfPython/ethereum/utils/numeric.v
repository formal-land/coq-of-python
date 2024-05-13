Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.utils.numeric".

Definition locals_stack : list Locals.t := [].

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

Axiom typing_imports_Sequence :
  IsImported globals "typing" "Sequence".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".

Axiom ethereum_base_types_imports_U32 :
  IsImported globals "ethereum.base_types" "U32".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Definition get_sign : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "value" ] in
    ltac:(M.monadic (
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
        Compare.lt (|
          M.get_name (| globals, locals_stack, "value" |),
          Constant.int 0
        |),
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
            Compare.eq (|
              M.get_name (| globals, locals_stack, "value" |),
              Constant.int 0
            |),
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

Axiom get_sign_in_globals :
  IsInGlobals globals "get_sign" (make_function get_sign).

Definition ceil32 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "value" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "ceiling" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          Constant.int 32
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "remainder" ,
      BinOp.mod_ (|
        M.get_name (| globals, locals_stack, "value" |),
        M.get_name (| globals, locals_stack, "ceiling" |)
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "remainder" |),
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "value" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          BinOp.sub (|
            BinOp.add (|
              M.get_name (| globals, locals_stack, "value" |),
              M.get_name (| globals, locals_stack, "ceiling" |)
            |),
            M.get_name (| globals, locals_stack, "remainder" |)
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom ceil32_in_globals :
  IsInGlobals globals "ceil32" (make_function ceil32).

Definition is_prime : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "number" ] in
    ltac:(M.monadic (
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
        Compare.lt_e (|
          M.get_name (| globals, locals_stack, "number" |),
          Constant.int 1
        |),
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
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "x" |),
        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        Constant.int 2;
        BinOp.add (|
          M.call (|
            M.get_name (| globals, locals_stack, "int" |),
            make_list [
              BinOp.pow (|
                M.get_name (| globals, locals_stack, "number" |),
                Constant.float "0.5"
              |)
            ],
            make_dict []
          |),
          Constant.int 1
        |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.eq (|
                BinOp.mod_ (|
                  M.get_name (| globals, locals_stack, "number" |),
                  M.get_name (| globals, locals_stack, "x" |)
                |),
                Constant.int 0
              |),
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
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      Constant.bool true
    |) in
    M.pure Constant.None_)).

Axiom is_prime_in_globals :
  IsInGlobals globals "is_prime" (make_function is_prime).

Definition le_bytes_to_uint32_sequence : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "data" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "sequence" ,
      make_list []
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "i" |),
        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        Constant.int 0;
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_name (| globals, locals_stack, "data" |)
          ],
          make_dict []
        |);
        Constant.int 4
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "sequence" |), "append" |),
    make_list [
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U32" |), "from_le_bytes" |),
        make_list [
          M.slice (|
            M.get_name (| globals, locals_stack, "data" |),
            M.get_name (| globals, locals_stack, "i" |),
            BinOp.add (|
              M.get_name (| globals, locals_stack, "i" |),
              Constant.int 4
            |),
            Constant.None_
          |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "tuple" |),
        make_list [
          M.get_name (| globals, locals_stack, "sequence" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom le_bytes_to_uint32_sequence_in_globals :
  IsInGlobals globals "le_bytes_to_uint32_sequence" (make_function le_bytes_to_uint32_sequence).

Definition le_uint32_sequence_to_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "sequence" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "result_bytes" ,
      Constant.bytes ""
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "item" |),
        M.get_name (| globals, locals_stack, "sequence" |),
        ltac:(M.monadic (
          let _ := M.assign_op_local (|
            BinOp.add,
            "result_bytes",
            M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "item" |), "to_le_bytes4" |),
    make_list [],
    make_dict []
  |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "result_bytes" |)
    |) in
    M.pure Constant.None_)).

Axiom le_uint32_sequence_to_bytes_in_globals :
  IsInGlobals globals "le_uint32_sequence_to_bytes" (make_function le_uint32_sequence_to_bytes).

Definition le_uint32_sequence_to_uint : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "sequence" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "sequence_as_bytes" ,
      M.call (|
        M.get_name (| globals, locals_stack, "le_uint32_sequence_to_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "sequence" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_le_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "sequence_as_bytes" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom le_uint32_sequence_to_uint_in_globals :
  IsInGlobals globals "le_uint32_sequence_to_uint" (make_function le_uint32_sequence_to_uint).

Definition taylor_exponential : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "factor"; "numerator"; "denominator" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "i" ,
      Constant.int 1
    |) in
    let _ := M.assign_local (|
      "output" ,
      Constant.int 0
    |) in
    let _ := M.assign_local (|
      "numerator_accumulated" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "factor" |),
        M.get_name (| globals, locals_stack, "denominator" |)
      |)
    |) in
    let _ :=
      M.while (|
        Compare.gt (|
      M.get_name (| globals, locals_stack, "numerator_accumulated" |),
      Constant.int 0
    |),
        ltac:(M.monadic (
          let _ := M.assign_op_local (|
            BinOp.add,
            "output",
            M.get_name (| globals, locals_stack, "numerator_accumulated" |)
          |) in
          let _ := M.assign_local (|
            "numerator_accumulated" ,
            BinOp.floor_div (|
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "numerator_accumulated" |),
                M.get_name (| globals, locals_stack, "numerator" |)
              |),
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "denominator" |),
                M.get_name (| globals, locals_stack, "i" |)
              |)
            |)
          |) in
          let _ := M.assign_op_local (|
            BinOp.add,
            "i",
            Constant.int 1
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      BinOp.floor_div (|
        M.get_name (| globals, locals_stack, "output" |),
        M.get_name (| globals, locals_stack, "denominator" |)
      |)
    |) in
    M.pure Constant.None_)).

Axiom taylor_exponential_in_globals :
  IsInGlobals globals "taylor_exponential" (make_function taylor_exponential).
