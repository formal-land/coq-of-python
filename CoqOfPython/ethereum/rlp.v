Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.rlp".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
.. _rlp:

Recursive Length Prefix (RLP) Encoding
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Defines the serialization and deserialization format used throughout Ethereum.
".

Axiom dataclasses_imports_astuple :
  IsImported globals "dataclasses" "astuple".
Axiom dataclasses_imports_fields :
  IsImported globals "dataclasses" "fields".
Axiom dataclasses_imports_is_dataclass :
  IsImported globals "dataclasses" "is_dataclass".

Axiom typing_imports_Any :
  IsImported globals "typing" "Any".
Axiom typing_imports_List :
  IsImported globals "typing" "List".
Axiom typing_imports_Sequence :
  IsImported globals "typing" "Sequence".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".
Axiom typing_imports_Type :
  IsImported globals "typing" "Type".
Axiom typing_imports_TypeVar :
  IsImported globals "typing" "TypeVar".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".
Axiom typing_imports_cast :
  IsImported globals "typing" "cast".

Axiom ethereum_crypto_hash_imports_Hash32 :
  IsImported globals "ethereum.crypto.hash" "Hash32".
Axiom ethereum_crypto_hash_imports_keccak256 :
  IsImported globals "ethereum.crypto.hash" "keccak256".

Axiom ethereum_exceptions_imports_RLPDecodingError :
  IsImported globals "ethereum.exceptions" "RLPDecodingError".
Axiom ethereum_exceptions_imports_RLPEncodingError :
  IsImported globals "ethereum.exceptions" "RLPEncodingError".

Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".
Axiom ethereum_base_types_imports_Bytes20 :
  IsImported globals "ethereum.base_types" "Bytes20".
Axiom ethereum_base_types_imports_FixedBytes :
  IsImported globals "ethereum.base_types" "FixedBytes".
Axiom ethereum_base_types_imports_FixedUint :
  IsImported globals "ethereum.base_types" "FixedUint".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Definition RLP : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, locals_stack, "Any" |)
)).

Definition encode : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "raw_data" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Encodes `raw_data` into a sequence of bytes using RLP.

    Parameters
    ----------
    raw_data :
        A `Bytes`, `Uint`, `Uint256` or sequence of `RLP` encodable
        objects.

    Returns
    -------
    encoded : `ethereum.base_types.Bytes`
        The RLP encoded bytes representing `raw_data`.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "raw_data" |);
            make_tuple [ M.get_name (| globals, locals_stack, "bytearray" |); M.get_name (| globals, locals_stack, "bytes" |) ]
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "encode_bytes" |),
            make_list [
              M.get_name (| globals, locals_stack, "raw_data" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, locals_stack, "isinstance" |),
              make_list [
                M.get_name (| globals, locals_stack, "raw_data" |);
                make_tuple [ M.get_name (| globals, locals_stack, "Uint" |); M.get_name (| globals, locals_stack, "FixedUint" |) ]
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.call (|
                M.get_name (| globals, locals_stack, "encode" |),
                make_list [
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "raw_data" |), "to_be_bytes" |),
                    make_list [],
                    make_dict []
                  |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                M.call (|
                  M.get_name (| globals, locals_stack, "isinstance" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "raw_data" |);
                    M.get_name (| globals, locals_stack, "str" |)
                  ],
                  make_dict []
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "encode_bytes" |),
                    make_list [
                      M.call (|
                        M.get_field (| M.get_name (| globals, locals_stack, "raw_data" |), "encode" |),
                        make_list [],
                        make_dict []
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    M.call (|
                      M.get_name (| globals, locals_stack, "isinstance" |),
                      make_list [
                        M.get_name (| globals, locals_stack, "raw_data" |);
                        M.get_name (| globals, locals_stack, "bool" |)
                      ],
                      make_dict []
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ :=
                      (* if *)
                      M.if_then_else (|
                        M.get_name (| globals, locals_stack, "raw_data" |),
                      (* then *)
                      ltac:(M.monadic (
                        let _ := M.return_ (|
                          M.call (|
                            M.get_name (| globals, locals_stack, "encode_bytes" |),
                            make_list [
                              Constant.bytes "01"
                            ],
                            make_dict []
                          |)
                        |) in
                        M.pure Constant.None_
                      (* else *)
                      )), ltac:(M.monadic (
                        let _ := M.return_ (|
                          M.call (|
                            M.get_name (| globals, locals_stack, "encode_bytes" |),
                            make_list [
                              Constant.bytes ""
                            ],
                            make_dict []
                          |)
                        |) in
                        M.pure Constant.None_
                      )) |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    let _ :=
                      (* if *)
                      M.if_then_else (|
                        M.call (|
                          M.get_name (| globals, locals_stack, "isinstance" |),
                          make_list [
                            M.get_name (| globals, locals_stack, "raw_data" |);
                            M.get_name (| globals, locals_stack, "Sequence" |)
                          ],
                          make_dict []
                        |),
                      (* then *)
                      ltac:(M.monadic (
                        let _ := M.return_ (|
                          M.call (|
                            M.get_name (| globals, locals_stack, "encode_sequence" |),
                            make_list [
                              M.get_name (| globals, locals_stack, "raw_data" |)
                            ],
                            make_dict []
                          |)
                        |) in
                        M.pure Constant.None_
                      (* else *)
                      )), ltac:(M.monadic (
                        let _ :=
                          (* if *)
                          M.if_then_else (|
                            M.call (|
                              M.get_name (| globals, locals_stack, "is_dataclass" |),
                              make_list [
                                M.get_name (| globals, locals_stack, "raw_data" |)
                              ],
                              make_dict []
                            |),
                          (* then *)
                          ltac:(M.monadic (
                            let _ := M.return_ (|
                              M.call (|
                                M.get_name (| globals, locals_stack, "encode" |),
                                make_list [
                                  M.call (|
                                    M.get_name (| globals, locals_stack, "astuple" |),
                                    make_list [
                                      M.get_name (| globals, locals_stack, "raw_data" |)
                                    ],
                                    make_dict []
                                  |)
                                ],
                                make_dict []
                              |)
                            |) in
                            M.pure Constant.None_
                          (* else *)
                          )), ltac:(M.monadic (
                            let _ := M.raise (| Some (M.call (|
                              M.get_name (| globals, locals_stack, "RLPEncodingError" |),
                              make_list [
                                M.call (|
                                  M.get_field (| Constant.str "RLP Encoding of type {} is not supported", "format" |),
                                  make_list [
                                    M.call (|
                                      M.get_name (| globals, locals_stack, "type" |),
                                      make_list [
                                        M.get_name (| globals, locals_stack, "raw_data" |)
                                      ],
                                      make_dict []
                                    |)
                                  ],
                                  make_dict []
                                |)
                              ],
                              make_dict []
                            |)) |) in
                            M.pure Constant.None_
                          )) |) in
                        M.pure Constant.None_
                      )) |) in
                    M.pure Constant.None_
                  )) |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom encode_in_globals :
  IsInGlobals globals "encode" (make_function encode).

Definition encode_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "raw_bytes" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Encodes `raw_bytes`, a sequence of bytes, using RLP.

    Parameters
    ----------
    raw_bytes :
        Bytes to encode with RLP.

    Returns
    -------
    encoded : `ethereum.base_types.Bytes`
        The RLP encoded bytes representing `raw_bytes`.
    " in
    let _ := M.assign_local (|
      "len_raw_data" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "raw_bytes" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.eq (|
            M.get_name (| globals, locals_stack, "len_raw_data" |),
            Constant.int 1
          |),
          ltac:(M.monadic (
            Compare.lt (|
              M.get_subscript (|
                M.get_name (| globals, locals_stack, "raw_bytes" |),
                Constant.int 0
              |),
              Constant.int 128
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "raw_bytes" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (|
              M.get_name (| globals, locals_stack, "len_raw_data" |),
              Constant.int 56
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              BinOp.add (|
                M.call (|
                  M.get_name (| globals, locals_stack, "bytes" |),
                  make_list [
                    make_list [
                      BinOp.add (|
                        Constant.int 128,
                        M.get_name (| globals, locals_stack, "len_raw_data" |)
                      |)
                    ]
                  ],
                  make_dict []
                |),
                M.get_name (| globals, locals_stack, "raw_bytes" |)
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "len_raw_data_as_be" ,
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "len_raw_data" |), "to_be_bytes" |),
                make_list [],
                make_dict []
              |)
            |) in
            let _ := M.return_ (|
              BinOp.add (|
                BinOp.add (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "bytes" |),
                    make_list [
                      make_list [
                        BinOp.add (|
                          Constant.int 183,
                          M.call (|
                            M.get_name (| globals, locals_stack, "len" |),
                            make_list [
                              M.get_name (| globals, locals_stack, "len_raw_data_as_be" |)
                            ],
                            make_dict []
                          |)
                        |)
                      ]
                    ],
                    make_dict []
                  |),
                  M.get_name (| globals, locals_stack, "len_raw_data_as_be" |)
                |),
                M.get_name (| globals, locals_stack, "raw_bytes" |)
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom encode_bytes_in_globals :
  IsInGlobals globals "encode_bytes" (make_function encode_bytes).

Definition encode_sequence : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "raw_sequence" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Encodes a list of RLP encodable objects (`raw_sequence`) using RLP.

    Parameters
    ----------
    raw_sequence :
            Sequence of RLP encodable objects.

    Returns
    -------
    encoded : `ethereum.base_types.Bytes`
        The RLP encoded bytes representing `raw_sequence`.
    " in
    let _ := M.assign_local (|
      "joined_encodings" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_joined_encodings" |),
        make_list [
          M.get_name (| globals, locals_stack, "raw_sequence" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "len_joined_encodings" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "joined_encodings" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, locals_stack, "len_joined_encodings" |),
          Constant.int 56
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          BinOp.add (|
            M.call (|
              M.get_name (| globals, locals_stack, "Bytes" |),
              make_list [
                make_list [
                  BinOp.add (|
                    Constant.int 192,
                    M.get_name (| globals, locals_stack, "len_joined_encodings" |)
                  |)
                ]
              ],
              make_dict []
            |),
            M.get_name (| globals, locals_stack, "joined_encodings" |)
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "len_joined_encodings_as_be" ,
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "len_joined_encodings" |), "to_be_bytes" |),
            make_list [],
            make_dict []
          |)
        |) in
        let _ := M.return_ (|
          BinOp.add (|
            BinOp.add (|
              M.call (|
                M.get_name (| globals, locals_stack, "Bytes" |),
                make_list [
                  make_list [
                    BinOp.add (|
                      Constant.int 247,
                      M.call (|
                        M.get_name (| globals, locals_stack, "len" |),
                        make_list [
                          M.get_name (| globals, locals_stack, "len_joined_encodings_as_be" |)
                        ],
                        make_dict []
                      |)
                    |)
                  ]
                ],
                make_dict []
              |),
              M.get_name (| globals, locals_stack, "len_joined_encodings_as_be" |)
            |),
            M.get_name (| globals, locals_stack, "joined_encodings" |)
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom encode_sequence_in_globals :
  IsInGlobals globals "encode_sequence" (make_function encode_sequence).

Definition get_joined_encodings : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "raw_sequence" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Obtain concatenation of rlp encoding for each item in the sequence
    raw_sequence.

    Parameters
    ----------
    raw_sequence :
        Sequence to encode with RLP.

    Returns
    -------
    joined_encodings : `ethereum.base_types.Bytes`
        The concatenated RLP encoded bytes for each item in sequence
        raw_sequence.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| Constant.bytes "", "join" |),
        make_list [
          Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom get_joined_encodings_in_globals :
  IsInGlobals globals "get_joined_encodings" (make_function get_joined_encodings).

Definition decode : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "encoded_data" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Decodes an integer, byte sequence, or list of RLP encodable objects
    from the byte sequence `encoded_data`, using RLP.

    Parameters
    ----------
    encoded_data :
        A sequence of bytes, in RLP form.

    Returns
    -------
    decoded_data : `RLP`
        Object decoded from `encoded_data`.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "encoded_data" |)
            ],
            make_dict []
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.call (|
          M.get_name (| globals, locals_stack, "RLPDecodingError" |),
          make_list [
            Constant.str "Cannot decode empty bytestring"
          ],
          make_dict []
        |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.get_subscript (|
            M.get_name (| globals, locals_stack, "encoded_data" |),
            Constant.int 0
          |),
          Constant.int 191
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "decode_to_bytes" |),
            make_list [
              M.get_name (| globals, locals_stack, "encoded_data" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "decode_to_sequence" |),
            make_list [
              M.get_name (| globals, locals_stack, "encoded_data" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom decode_in_globals :
  IsInGlobals globals "decode" (make_function decode).

Definition T : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "T"
    ],
    make_dict []
  |)
)).

Definition decode_to : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "encoded_data" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Decode the bytes in `encoded_data` to an object of type `cls`. `cls` can be
    a `Bytes` subclass, a dataclass, `Uint`, `U256` or `Tuple[cls]`.

    Parameters
    ----------
    cls: `Type[T]`
        The type to decode to.
    encoded_data :
        A sequence of bytes, in RLP form.

    Returns
    -------
    decoded_data : `T`
        Object decoded from `encoded_data`.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "_decode_to" |),
        make_list [
          M.get_name (| globals, locals_stack, "cls" |);
          M.call (|
            M.get_name (| globals, locals_stack, "decode" |),
            make_list [
              M.get_name (| globals, locals_stack, "encoded_data" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom decode_to_in_globals :
  IsInGlobals globals "decode_to" (make_function decode_to).

Definition _decode_to : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "raw_rlp" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Decode the rlp structure in `encoded_data` to an object of type `cls`.
    `cls` can be a `Bytes` subclass, a dataclass, `Uint`, `U256`,
    `Tuple[cls, ...]`, `Tuple[cls1, cls2]` or `Union[Bytes, cls]`.

    Parameters
    ----------
    cls: `Type[T]`
        The type to decode to.
    raw_rlp :
        A decoded rlp structure.

    Returns
    -------
    decoded_data : `T`
        Object decoded from `encoded_data`.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          M.call (|
            M.get_name (| globals, locals_stack, "isinstance" |),
            make_list [
              M.get_name (| globals, locals_stack, "cls" |);
              M.call (|
                M.get_name (| globals, locals_stack, "type" |),
                make_list [
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "Tuple" |),
                    make_tuple [ M.get_name (| globals, locals_stack, "Uint" |); Constant.ellipsis ]
                  |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "_name" |),
              Constant.str "Tuple"
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (|
              M.get_name (| globals, locals_stack, "isinstance" |),
              make_list [
                M.get_name (| globals, locals_stack, "raw_rlp" |);
                M.get_name (| globals, locals_stack, "list" |)
              ],
              make_dict []
            |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_subscript (|
                M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |),
                Constant.int 1
              |),
              Constant.ellipsis
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "args" ,
              make_list []
            |) in
            let _ :=
              M.for_ (|
                M.get_name (| globals, locals_stack, "raw_item" |),
                M.get_name (| globals, locals_stack, "raw_rlp" |),
                ltac:(M.monadic (
                  let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "args" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, locals_stack, "_decode_to" |),
        make_list [
          M.get_subscript (|
            M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |),
            Constant.int 0
          |);
          M.get_name (| globals, locals_stack, "raw_item" |)
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
                  M.get_name (| globals, locals_stack, "args" |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "args" ,
              make_list []
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.not_eq (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "raw_rlp" |)
                    ],
                    make_dict []
                  |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |)
                    ],
                    make_dict []
                  |)
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ :=
              M.for_ (|
                make_tuple [ M.get_name (| globals, locals_stack, "t" |); M.get_name (| globals, locals_stack, "raw_item" |) ],
                M.call (|
      M.get_name (| globals, locals_stack, "zip" |),
      make_list [
        M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |);
        M.get_name (| globals, locals_stack, "raw_rlp" |)
      ],
      make_dict []
    |),
                ltac:(M.monadic (
                  let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "args" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, locals_stack, "_decode_to" |),
        make_list [
          M.get_name (| globals, locals_stack, "t" |);
          M.get_name (| globals, locals_stack, "raw_item" |)
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
                  M.get_name (| globals, locals_stack, "args" |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_name (| globals, locals_stack, "cls" |),
              M.get_subscript (|
                M.get_name (| globals, locals_stack, "Union" |),
                make_tuple [ M.get_name (| globals, locals_stack, "Bytes0" |); M.get_name (| globals, locals_stack, "Bytes20" |) ]
              |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                UnOp.not (| M.call (|
                  M.get_name (| globals, locals_stack, "isinstance" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "raw_rlp" |);
                    M.get_name (| globals, locals_stack, "Bytes" |)
                  ],
                  make_dict []
                |) |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.eq (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "raw_rlp" |)
                    ],
                    make_dict []
                  |),
                  Constant.int 0
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "Bytes0" |),
                    make_list [],
                    make_dict []
                  |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.eq (|
                      M.call (|
                        M.get_name (| globals, locals_stack, "len" |),
                        make_list [
                          M.get_name (| globals, locals_stack, "raw_rlp" |)
                        ],
                        make_dict []
                      |),
                      Constant.int 20
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.return_ (|
                      M.call (|
                        M.get_name (| globals, locals_stack, "Bytes20" |),
                        make_list [
                          M.get_name (| globals, locals_stack, "raw_rlp" |)
                        ],
                        make_dict []
                      |)
                    |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    let _ := M.raise (| Some (M.call (|
                      M.get_name (| globals, locals_stack, "RLPDecodingError" |),
                      make_list [
                        M.call (|
                          M.get_field (| Constant.str "Bytes has length {}, expected 0 or 20", "format" |),
                          make_list [
                            M.call (|
                              M.get_name (| globals, locals_stack, "len" |),
                              make_list [
                                M.get_name (| globals, locals_stack, "raw_rlp" |)
                              ],
                              make_dict []
                            |)
                          ],
                          make_dict []
                        |)
                      ],
                      make_dict []
                    |)) |) in
                    M.pure Constant.None_
                  )) |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                BoolOp.and (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "isinstance" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "cls" |);
                      M.call (|
                        M.get_name (| globals, locals_stack, "type" |),
                        make_list [
                          M.get_subscript (|
                            M.get_name (| globals, locals_stack, "List" |),
                            M.get_name (| globals, locals_stack, "Bytes" |)
                          |)
                        ],
                        make_dict []
                      |)
                    ],
                    make_dict []
                  |),
                  ltac:(M.monadic (
                    Compare.eq (|
                      M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "_name" |),
                      Constant.str "List"
                    |)
                  ))
                |),
              (* then *)
              ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    UnOp.not (| M.call (|
                      M.get_name (| globals, locals_stack, "isinstance" |),
                      make_list [
                        M.get_name (| globals, locals_stack, "raw_rlp" |);
                        M.get_name (| globals, locals_stack, "list" |)
                      ],
                      make_dict []
                    |) |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    M.pure Constant.None_
                  )) |) in
                let _ := M.assign_local (|
                  "items" ,
                  make_list []
                |) in
                let _ :=
                  M.for_ (|
                    M.get_name (| globals, locals_stack, "raw_item" |),
                    M.get_name (| globals, locals_stack, "raw_rlp" |),
                    ltac:(M.monadic (
                      let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "items" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, locals_stack, "_decode_to" |),
        make_list [
          M.get_subscript (|
            M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |),
            Constant.int 0
          |);
          M.get_name (| globals, locals_stack, "raw_item" |)
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
                  M.get_name (| globals, locals_stack, "items" |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    BoolOp.and (|
                      M.call (|
                        M.get_name (| globals, locals_stack, "isinstance" |),
                        make_list [
                          M.get_name (| globals, locals_stack, "cls" |);
                          M.call (|
                            M.get_name (| globals, locals_stack, "type" |),
                            make_list [
                              M.get_subscript (|
                                M.get_name (| globals, locals_stack, "Union" |),
                                make_tuple [ M.get_name (| globals, locals_stack, "Bytes" |); M.get_subscript (|
                                  M.get_name (| globals, locals_stack, "List" |),
                                  M.get_name (| globals, locals_stack, "Bytes" |)
                                |) ]
                              |)
                            ],
                            make_dict []
                          |)
                        ],
                        make_dict []
                      |),
                      ltac:(M.monadic (
                        Compare.eq (|
                          M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__origin__" |),
                          M.get_name (| globals, locals_stack, "Union" |)
                        |)
                      ))
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ :=
                      (* if *)
                      M.if_then_else (|
                        BoolOp.or (|
                          Compare.not_eq (|
                            M.call (|
                              M.get_name (| globals, locals_stack, "len" |),
                              make_list [
                                M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |)
                              ],
                              make_dict []
                            |),
                            Constant.int 2
                          |),
                          ltac:(M.monadic (
                            Compare.not_in (|
                              M.get_name (| globals, locals_stack, "Bytes" |),
                              M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |)
                            |)
                          ))
                        |),
                      (* then *)
                      ltac:(M.monadic (
                        let _ := M.raise (| Some (M.call (|
                          M.get_name (| globals, locals_stack, "RLPDecodingError" |),
                          make_list [
                            M.call (|
                              M.get_field (| Constant.str "RLP Decoding to type {} is not supported", "format" |),
                              make_list [
                                M.get_name (| globals, locals_stack, "cls" |)
                              ],
                              make_dict []
                            |)
                          ],
                          make_dict []
                        |)) |) in
                        M.pure Constant.None_
                      (* else *)
                      )), ltac:(M.monadic (
                        M.pure Constant.None_
                      )) |) in
                    let _ :=
                      (* if *)
                      M.if_then_else (|
                        M.call (|
                          M.get_name (| globals, locals_stack, "isinstance" |),
                          make_list [
                            M.get_name (| globals, locals_stack, "raw_rlp" |);
                            M.get_name (| globals, locals_stack, "Bytes" |)
                          ],
                          make_dict []
                        |),
                      (* then *)
                      ltac:(M.monadic (
                        let _ := M.return_ (|
                          M.get_name (| globals, locals_stack, "raw_rlp" |)
                        |) in
                        M.pure Constant.None_
                      (* else *)
                      )), ltac:(M.monadic (
                        let _ :=
                          (* if *)
                          M.if_then_else (|
                            Compare.eq (|
                              M.get_subscript (|
                                M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |),
                                Constant.int 0
                              |),
                              M.get_name (| globals, locals_stack, "Bytes" |)
                            |),
                          (* then *)
                          ltac:(M.monadic (
                            let _ := M.return_ (|
                              M.call (|
                                M.get_name (| globals, locals_stack, "_decode_to" |),
                                make_list [
                                  M.get_subscript (|
                                    M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |),
                                    Constant.int 1
                                  |);
                                  M.get_name (| globals, locals_stack, "raw_rlp" |)
                                ],
                                make_dict []
                              |)
                            |) in
                            M.pure Constant.None_
                          (* else *)
                          )), ltac:(M.monadic (
                            let _ := M.return_ (|
                              M.call (|
                                M.get_name (| globals, locals_stack, "_decode_to" |),
                                make_list [
                                  M.get_subscript (|
                                    M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__args__" |),
                                    Constant.int 0
                                  |);
                                  M.get_name (| globals, locals_stack, "raw_rlp" |)
                                ],
                                make_dict []
                              |)
                            |) in
                            M.pure Constant.None_
                          )) |) in
                        M.pure Constant.None_
                      )) |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    let _ :=
                      (* if *)
                      M.if_then_else (|
                        M.call (|
                          M.get_name (| globals, locals_stack, "issubclass" |),
                          make_list [
                            M.get_name (| globals, locals_stack, "cls" |);
                            M.get_name (| globals, locals_stack, "bool" |)
                          ],
                          make_dict []
                        |),
                      (* then *)
                      ltac:(M.monadic (
                        let _ :=
                          (* if *)
                          M.if_then_else (|
                            Compare.eq (|
                              M.get_name (| globals, locals_stack, "raw_rlp" |),
                              Constant.bytes "01"
                            |),
                          (* then *)
                          ltac:(M.monadic (
                            let _ := M.return_ (|
                              M.call (|
                                M.get_name (| globals, locals_stack, "cls" |),
                                make_list [
                                  Constant.bool true
                                ],
                                make_dict []
                              |)
                            |) in
                            M.pure Constant.None_
                          (* else *)
                          )), ltac:(M.monadic (
                            let _ :=
                              (* if *)
                              M.if_then_else (|
                                Compare.eq (|
                                  M.get_name (| globals, locals_stack, "raw_rlp" |),
                                  Constant.bytes ""
                                |),
                              (* then *)
                              ltac:(M.monadic (
                                let _ := M.return_ (|
                                  M.call (|
                                    M.get_name (| globals, locals_stack, "cls" |),
                                    make_list [
                                      Constant.bool false
                                    ],
                                    make_dict []
                                  |)
                                |) in
                                M.pure Constant.None_
                              (* else *)
                              )), ltac:(M.monadic (
                                let _ := M.raise (| Some (M.call (|
                                  M.get_name (| globals, locals_stack, "TypeError" |),
                                  make_list [
                                    M.call (|
                                      M.get_field (| Constant.str "Cannot decode {} as {}", "format" |),
                                      make_list [
                                        M.get_name (| globals, locals_stack, "raw_rlp" |);
                                        M.get_name (| globals, locals_stack, "cls" |)
                                      ],
                                      make_dict []
                                    |)
                                  ],
                                  make_dict []
                                |)) |) in
                                M.pure Constant.None_
                              )) |) in
                            M.pure Constant.None_
                          )) |) in
                        M.pure Constant.None_
                      (* else *)
                      )), ltac:(M.monadic (
                        let _ :=
                          (* if *)
                          M.if_then_else (|
                            M.call (|
                              M.get_name (| globals, locals_stack, "issubclass" |),
                              make_list [
                                M.get_name (| globals, locals_stack, "cls" |);
                                M.get_name (| globals, locals_stack, "FixedBytes" |)
                              ],
                              make_dict []
                            |),
                          (* then *)
                          ltac:(M.monadic (
                            let _ :=
                              (* if *)
                              M.if_then_else (|
                                UnOp.not (| M.call (|
                                  M.get_name (| globals, locals_stack, "isinstance" |),
                                  make_list [
                                    M.get_name (| globals, locals_stack, "raw_rlp" |);
                                    M.get_name (| globals, locals_stack, "Bytes" |)
                                  ],
                                  make_dict []
                                |) |),
                              (* then *)
                              ltac:(M.monadic (
                                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                                M.pure Constant.None_
                              (* else *)
                              )), ltac:(M.monadic (
                                M.pure Constant.None_
                              )) |) in
                            let _ :=
                              (* if *)
                              M.if_then_else (|
                                Compare.not_eq (|
                                  M.call (|
                                    M.get_name (| globals, locals_stack, "len" |),
                                    make_list [
                                      M.get_name (| globals, locals_stack, "raw_rlp" |)
                                    ],
                                    make_dict []
                                  |),
                                  M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "LENGTH" |)
                                |),
                              (* then *)
                              ltac:(M.monadic (
                                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                                M.pure Constant.None_
                              (* else *)
                              )), ltac:(M.monadic (
                                M.pure Constant.None_
                              )) |) in
                            let _ := M.return_ (|
                              M.call (|
                                M.get_name (| globals, locals_stack, "cls" |),
                                make_list [
                                  M.get_name (| globals, locals_stack, "raw_rlp" |)
                                ],
                                make_dict []
                              |)
                            |) in
                            M.pure Constant.None_
                          (* else *)
                          )), ltac:(M.monadic (
                            let _ :=
                              (* if *)
                              M.if_then_else (|
                                M.call (|
                                  M.get_name (| globals, locals_stack, "issubclass" |),
                                  make_list [
                                    M.get_name (| globals, locals_stack, "cls" |);
                                    M.get_name (| globals, locals_stack, "Bytes" |)
                                  ],
                                  make_dict []
                                |),
                              (* then *)
                              ltac:(M.monadic (
                                let _ :=
                                  (* if *)
                                  M.if_then_else (|
                                    UnOp.not (| M.call (|
                                      M.get_name (| globals, locals_stack, "isinstance" |),
                                      make_list [
                                        M.get_name (| globals, locals_stack, "raw_rlp" |);
                                        M.get_name (| globals, locals_stack, "Bytes" |)
                                      ],
                                      make_dict []
                                    |) |),
                                  (* then *)
                                  ltac:(M.monadic (
                                    let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                                    M.pure Constant.None_
                                  (* else *)
                                  )), ltac:(M.monadic (
                                    M.pure Constant.None_
                                  )) |) in
                                let _ := M.return_ (|
                                  M.get_name (| globals, locals_stack, "raw_rlp" |)
                                |) in
                                M.pure Constant.None_
                              (* else *)
                              )), ltac:(M.monadic (
                                let _ :=
                                  (* if *)
                                  M.if_then_else (|
                                    M.call (|
                                      M.get_name (| globals, locals_stack, "issubclass" |),
                                      make_list [
                                        M.get_name (| globals, locals_stack, "cls" |);
                                        make_tuple [ M.get_name (| globals, locals_stack, "Uint" |); M.get_name (| globals, locals_stack, "FixedUint" |) ]
                                      ],
                                      make_dict []
                                    |),
                                  (* then *)
                                  ltac:(M.monadic (
                                    let _ :=
                                      (* if *)
                                      M.if_then_else (|
                                        UnOp.not (| M.call (|
                                          M.get_name (| globals, locals_stack, "isinstance" |),
                                          make_list [
                                            M.get_name (| globals, locals_stack, "raw_rlp" |);
                                            M.get_name (| globals, locals_stack, "Bytes" |)
                                          ],
                                          make_dict []
                                        |) |),
                                      (* then *)
                                      ltac:(M.monadic (
                                        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                                        M.pure Constant.None_
                                      (* else *)
                                      )), ltac:(M.monadic (
                                        M.pure Constant.None_
                                      )) |) in
(* At stmt: unsupported node type: Try *)
                                    M.pure Constant.None_
                                  (* else *)
                                  )), ltac:(M.monadic (
                                    let _ :=
                                      (* if *)
                                      M.if_then_else (|
                                        M.call (|
                                          M.get_name (| globals, locals_stack, "is_dataclass" |),
                                          make_list [
                                            M.get_name (| globals, locals_stack, "cls" |)
                                          ],
                                          make_dict []
                                        |),
                                      (* then *)
                                      ltac:(M.monadic (
                                        let _ :=
                                          (* if *)
                                          M.if_then_else (|
                                            UnOp.not (| M.call (|
                                              M.get_name (| globals, locals_stack, "isinstance" |),
                                              make_list [
                                                M.get_name (| globals, locals_stack, "raw_rlp" |);
                                                M.get_name (| globals, locals_stack, "list" |)
                                              ],
                                              make_dict []
                                            |) |),
                                          (* then *)
                                          ltac:(M.monadic (
                                            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                                            M.pure Constant.None_
                                          (* else *)
                                          )), ltac:(M.monadic (
                                            M.pure Constant.None_
                                          )) |) in
                                        let _ := M.assert (| M.call (|
    M.get_name (| globals, locals_stack, "isinstance" |),
    make_list [
      M.get_name (| globals, locals_stack, "raw_rlp" |);
      M.get_name (| globals, locals_stack, "list" |)
    ],
    make_dict []
  |) |) in
                                        let _ := M.assign_local (|
                                          "args" ,
                                          make_list []
                                        |) in
                                        let _ :=
                                          (* if *)
                                          M.if_then_else (|
                                            Compare.not_eq (|
                                              M.call (|
                                                M.get_name (| globals, locals_stack, "len" |),
                                                make_list [
                                                  M.call (|
                                                    M.get_name (| globals, locals_stack, "fields" |),
                                                    make_list [
                                                      M.get_name (| globals, locals_stack, "cls" |)
                                                    ],
                                                    make_dict []
                                                  |)
                                                ],
                                                make_dict []
                                              |),
                                              M.call (|
                                                M.get_name (| globals, locals_stack, "len" |),
                                                make_list [
                                                  M.get_name (| globals, locals_stack, "raw_rlp" |)
                                                ],
                                                make_dict []
                                              |)
                                            |),
                                          (* then *)
                                          ltac:(M.monadic (
                                            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                                            M.pure Constant.None_
                                          (* else *)
                                          )), ltac:(M.monadic (
                                            M.pure Constant.None_
                                          )) |) in
                                        let _ :=
                                          M.for_ (|
                                            make_tuple [ M.get_name (| globals, locals_stack, "field" |); M.get_name (| globals, locals_stack, "rlp_item" |) ],
                                            M.call (|
      M.get_name (| globals, locals_stack, "zip" |),
      make_list [
        M.call (|
          M.get_name (| globals, locals_stack, "fields" |),
          make_list [
            M.get_name (| globals, locals_stack, "cls" |)
          ],
          make_dict []
        |);
        M.get_name (| globals, locals_stack, "raw_rlp" |)
      ],
      make_dict []
    |),
                                            ltac:(M.monadic (
                                              let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "args" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, locals_stack, "_decode_to" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "field" |), "type" |);
          M.get_name (| globals, locals_stack, "rlp_item" |)
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
                                            M.get_name (| globals, locals_stack, "cast" |),
                                            make_list [
                                              M.get_name (| globals, locals_stack, "T" |);
                                              M.call (|
                                                M.get_name (| globals, locals_stack, "cls" |),
                                                M.get_name (| globals, locals_stack, "args" |),
                                                make_dict []
                                              |)
                                            ],
                                            make_dict []
                                          |)
                                        |) in
                                        M.pure Constant.None_
                                      (* else *)
                                      )), ltac:(M.monadic (
                                        let _ := M.raise (| Some (M.call (|
                                          M.get_name (| globals, locals_stack, "RLPDecodingError" |),
                                          make_list [
                                            M.call (|
                                              M.get_field (| Constant.str "RLP Decoding to type {} is not supported", "format" |),
                                              make_list [
                                                M.get_name (| globals, locals_stack, "cls" |)
                                              ],
                                              make_dict []
                                            |)
                                          ],
                                          make_dict []
                                        |)) |) in
                                        M.pure Constant.None_
                                      )) |) in
                                    M.pure Constant.None_
                                  )) |) in
                                M.pure Constant.None_
                              )) |) in
                            M.pure Constant.None_
                          )) |) in
                        M.pure Constant.None_
                      )) |) in
                    M.pure Constant.None_
                  )) |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom _decode_to_in_globals :
  IsInGlobals globals "_decode_to" (make_function _decode_to).

Definition decode_to_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "encoded_bytes" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Decodes a rlp encoded byte stream assuming that the decoded data
    should be of type `bytes`.

    Parameters
    ----------
    encoded_bytes :
        RLP encoded byte stream.

    Returns
    -------
    decoded : `ethereum.base_types.Bytes`
        RLP decoded Bytes data
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.eq (|
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                M.get_name (| globals, locals_stack, "encoded_bytes" |)
              ],
              make_dict []
            |),
            Constant.int 1
          |),
          ltac:(M.monadic (
            Compare.lt (|
              M.get_subscript (|
                M.get_name (| globals, locals_stack, "encoded_bytes" |),
                Constant.int 0
              |),
              Constant.int 128
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "encoded_bytes" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt_e (|
              M.get_subscript (|
                M.get_name (| globals, locals_stack, "encoded_bytes" |),
                Constant.int 0
              |),
              Constant.int 183
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "len_raw_data" ,
              BinOp.sub (|
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "encoded_bytes" |),
                  Constant.int 0
                |),
                Constant.int 128
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.gt_e (|
                  M.get_name (| globals, locals_stack, "len_raw_data" |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "encoded_bytes" |)
                    ],
                    make_dict []
                  |)
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ := M.assign_local (|
              "raw_data" ,
              M.slice (|
                M.get_name (| globals, locals_stack, "encoded_bytes" |),
                Constant.int 1,
                BinOp.add (|
                  Constant.int 1,
                  M.get_name (| globals, locals_stack, "len_raw_data" |)
                |),
                Constant.None_
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                BoolOp.and (|
                  Compare.eq (|
                    M.get_name (| globals, locals_stack, "len_raw_data" |),
                    Constant.int 1
                  |),
                  ltac:(M.monadic (
                    Compare.lt (|
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "raw_data" |),
                        Constant.int 0
                      |),
                      Constant.int 128
                    |)
                  ))
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ := M.return_ (|
              M.get_name (| globals, locals_stack, "raw_data" |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "decoded_data_start_idx" ,
              BinOp.sub (|
                BinOp.add (|
                  Constant.int 1,
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "encoded_bytes" |),
                    Constant.int 0
                  |)
                |),
                Constant.int 183
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.gt_e (|
                  BinOp.sub (|
                    M.get_name (| globals, locals_stack, "decoded_data_start_idx" |),
                    Constant.int 1
                  |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "encoded_bytes" |)
                    ],
                    make_dict []
                  |)
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.eq (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "encoded_bytes" |),
                    Constant.int 1
                  |),
                  Constant.int 0
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ := M.assign_local (|
              "len_decoded_data" ,
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
                make_list [
                  M.slice (|
                    M.get_name (| globals, locals_stack, "encoded_bytes" |),
                    Constant.int 1,
                    M.get_name (| globals, locals_stack, "decoded_data_start_idx" |),
                    Constant.None_
                  |)
                ],
                make_dict []
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "len_decoded_data" |),
                  Constant.int 56
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ := M.assign_local (|
              "decoded_data_end_idx" ,
              BinOp.add (|
                M.get_name (| globals, locals_stack, "decoded_data_start_idx" |),
                M.get_name (| globals, locals_stack, "len_decoded_data" |)
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.gt_e (|
                  BinOp.sub (|
                    M.get_name (| globals, locals_stack, "decoded_data_end_idx" |),
                    Constant.int 1
                  |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "encoded_bytes" |)
                    ],
                    make_dict []
                  |)
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ := M.return_ (|
              M.slice (|
                M.get_name (| globals, locals_stack, "encoded_bytes" |),
                M.get_name (| globals, locals_stack, "decoded_data_start_idx" |),
                M.get_name (| globals, locals_stack, "decoded_data_end_idx" |),
                Constant.None_
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom decode_to_bytes_in_globals :
  IsInGlobals globals "decode_to_bytes" (make_function decode_to_bytes).

Definition decode_to_sequence : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "encoded_sequence" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Decodes a rlp encoded byte stream assuming that the decoded data
    should be of type `Sequence` of objects.

    Parameters
    ----------
    encoded_sequence :
        An RLP encoded Sequence.

    Returns
    -------
    decoded : `Sequence[RLP]`
        Sequence of objects decoded from `encoded_sequence`.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.get_subscript (|
            M.get_name (| globals, locals_stack, "encoded_sequence" |),
            Constant.int 0
          |),
          Constant.int 247
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "len_joined_encodings" ,
          BinOp.sub (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "encoded_sequence" |),
              Constant.int 0
            |),
            Constant.int 192
          |)
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt_e (|
              M.get_name (| globals, locals_stack, "len_joined_encodings" |),
              M.call (|
                M.get_name (| globals, locals_stack, "len" |),
                make_list [
                  M.get_name (| globals, locals_stack, "encoded_sequence" |)
                ],
                make_dict []
              |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.assign_local (|
          "joined_encodings" ,
          M.slice (|
            M.get_name (| globals, locals_stack, "encoded_sequence" |),
            Constant.int 1,
            BinOp.add (|
              Constant.int 1,
              M.get_name (| globals, locals_stack, "len_joined_encodings" |)
            |),
            Constant.None_
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "joined_encodings_start_idx" ,
          BinOp.sub (|
            BinOp.add (|
              Constant.int 1,
              M.get_subscript (|
                M.get_name (| globals, locals_stack, "encoded_sequence" |),
                Constant.int 0
              |)
            |),
            Constant.int 247
          |)
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt_e (|
              BinOp.sub (|
                M.get_name (| globals, locals_stack, "joined_encodings_start_idx" |),
                Constant.int 1
              |),
              M.call (|
                M.get_name (| globals, locals_stack, "len" |),
                make_list [
                  M.get_name (| globals, locals_stack, "encoded_sequence" |)
                ],
                make_dict []
              |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_subscript (|
                M.get_name (| globals, locals_stack, "encoded_sequence" |),
                Constant.int 1
              |),
              Constant.int 0
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.assign_local (|
          "len_joined_encodings" ,
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
            make_list [
              M.slice (|
                M.get_name (| globals, locals_stack, "encoded_sequence" |),
                Constant.int 1,
                M.get_name (| globals, locals_stack, "joined_encodings_start_idx" |),
                Constant.None_
              |)
            ],
            make_dict []
          |)
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (|
              M.get_name (| globals, locals_stack, "len_joined_encodings" |),
              Constant.int 56
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.assign_local (|
          "joined_encodings_end_idx" ,
          BinOp.add (|
            M.get_name (| globals, locals_stack, "joined_encodings_start_idx" |),
            M.get_name (| globals, locals_stack, "len_joined_encodings" |)
          |)
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt_e (|
              BinOp.sub (|
                M.get_name (| globals, locals_stack, "joined_encodings_end_idx" |),
                Constant.int 1
              |),
              M.call (|
                M.get_name (| globals, locals_stack, "len" |),
                make_list [
                  M.get_name (| globals, locals_stack, "encoded_sequence" |)
                ],
                make_dict []
              |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.assign_local (|
          "joined_encodings" ,
          M.slice (|
            M.get_name (| globals, locals_stack, "encoded_sequence" |),
            M.get_name (| globals, locals_stack, "joined_encodings_start_idx" |),
            M.get_name (| globals, locals_stack, "joined_encodings_end_idx" |),
            Constant.None_
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "decode_joined_encodings" |),
        make_list [
          M.get_name (| globals, locals_stack, "joined_encodings" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom decode_to_sequence_in_globals :
  IsInGlobals globals "decode_to_sequence" (make_function decode_to_sequence).

Definition decode_joined_encodings : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "joined_encodings" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Decodes `joined_encodings`, which is a concatenation of RLP encoded
    objects.

    Parameters
    ----------
    joined_encodings :
        concatenation of RLP encoded objects

    Returns
    -------
    decoded : `List[RLP]`
        A list of objects decoded from `joined_encodings`.
    " in
    let _ := M.assign_local (|
      "decoded_sequence" ,
      make_list []
    |) in
    let _ := M.assign_local (|
      "item_start_idx" ,
      Constant.int 0
    |) in
    let _ :=
      M.while (|
        Compare.lt (|
      M.get_name (| globals, locals_stack, "item_start_idx" |),
      M.call (|
        M.get_name (| globals, locals_stack, "len" |),
        make_list [
          M.get_name (| globals, locals_stack, "joined_encodings" |)
        ],
        make_dict []
      |)
    |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "encoded_item_length" ,
            M.call (|
              M.get_name (| globals, locals_stack, "decode_item_length" |),
              make_list [
                M.slice (|
                  M.get_name (| globals, locals_stack, "joined_encodings" |),
                  M.get_name (| globals, locals_stack, "item_start_idx" |),
                  Constant.None_,
                  Constant.None_
                |)
              ],
              make_dict []
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt_e (|
                BinOp.sub (|
                  BinOp.add (|
                    M.get_name (| globals, locals_stack, "item_start_idx" |),
                    M.get_name (| globals, locals_stack, "encoded_item_length" |)
                  |),
                  Constant.int 1
                |),
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "joined_encodings" |)
                  ],
                  make_dict []
                |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_local (|
            "encoded_item" ,
            M.slice (|
              M.get_name (| globals, locals_stack, "joined_encodings" |),
              M.get_name (| globals, locals_stack, "item_start_idx" |),
              BinOp.add (|
                M.get_name (| globals, locals_stack, "item_start_idx" |),
                M.get_name (| globals, locals_stack, "encoded_item_length" |)
              |),
              Constant.None_
            |)
          |) in
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "decoded_sequence" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, locals_stack, "decode" |),
        make_list [
          M.get_name (| globals, locals_stack, "encoded_item" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
          let _ := M.assign_op_local (|
            BinOp.add,
            "item_start_idx",
            M.get_name (| globals, locals_stack, "encoded_item_length" |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "decoded_sequence" |)
    |) in
    M.pure Constant.None_)).

Axiom decode_joined_encodings_in_globals :
  IsInGlobals globals "decode_joined_encodings" (make_function decode_joined_encodings).

Definition decode_item_length : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "encoded_data" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Find the length of the rlp encoding for the first object in the
    encoded sequence.
    Here `encoded_data` refers to concatenation of rlp encoding for each
    item in a sequence.

    NOTE - This is a helper function not described in the spec. It was
    introduced as the spec doesn't discuss about decoding the RLP encoded
    data.

    Parameters
    ----------
    encoded_data :
        RLP encoded data for a sequence of objects.

    Returns
    -------
    rlp_length : `int`
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "encoded_data" |)
            ],
            make_dict []
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "first_rlp_byte" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.get_subscript (|
            M.get_name (| globals, locals_stack, "encoded_data" |),
            Constant.int 0
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "length_length" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "decoded_data_length" ,
      Constant.int 0
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, locals_stack, "first_rlp_byte" |),
          Constant.int 128
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.int 1
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt_e (|
              M.get_name (| globals, locals_stack, "first_rlp_byte" |),
              Constant.int 183
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "decoded_data_length" ,
              BinOp.sub (|
                M.get_name (| globals, locals_stack, "first_rlp_byte" |),
                Constant.int 128
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.lt_e (|
                  M.get_name (| globals, locals_stack, "first_rlp_byte" |),
                  Constant.int 191
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.assign_local (|
                  "length_length" ,
                  BinOp.sub (|
                    M.get_name (| globals, locals_stack, "first_rlp_byte" |),
                    Constant.int 183
                  |)
                |) in
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.gt_e (|
                      M.get_name (| globals, locals_stack, "length_length" |),
                      M.call (|
                        M.get_name (| globals, locals_stack, "len" |),
                        make_list [
                          M.get_name (| globals, locals_stack, "encoded_data" |)
                        ],
                        make_dict []
                      |)
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    M.pure Constant.None_
                  )) |) in
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.eq (|
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "encoded_data" |),
                        Constant.int 1
                      |),
                      Constant.int 0
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    M.pure Constant.None_
                  )) |) in
                let _ := M.assign_local (|
                  "decoded_data_length" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
                    make_list [
                      M.slice (|
                        M.get_name (| globals, locals_stack, "encoded_data" |),
                        Constant.int 1,
                        BinOp.add (|
                          Constant.int 1,
                          M.get_name (| globals, locals_stack, "length_length" |)
                        |),
                        Constant.None_
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.lt_e (|
                      M.get_name (| globals, locals_stack, "first_rlp_byte" |),
                      Constant.int 247
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.assign_local (|
                      "decoded_data_length" ,
                      BinOp.sub (|
                        M.get_name (| globals, locals_stack, "first_rlp_byte" |),
                        Constant.int 192
                      |)
                    |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    let _ :=
                      (* if *)
                      M.if_then_else (|
                        Compare.lt_e (|
                          M.get_name (| globals, locals_stack, "first_rlp_byte" |),
                          Constant.int 255
                        |),
                      (* then *)
                      ltac:(M.monadic (
                        let _ := M.assign_local (|
                          "length_length" ,
                          BinOp.sub (|
                            M.get_name (| globals, locals_stack, "first_rlp_byte" |),
                            Constant.int 247
                          |)
                        |) in
                        let _ :=
                          (* if *)
                          M.if_then_else (|
                            Compare.gt_e (|
                              M.get_name (| globals, locals_stack, "length_length" |),
                              M.call (|
                                M.get_name (| globals, locals_stack, "len" |),
                                make_list [
                                  M.get_name (| globals, locals_stack, "encoded_data" |)
                                ],
                                make_dict []
                              |)
                            |),
                          (* then *)
                          ltac:(M.monadic (
                            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                            M.pure Constant.None_
                          (* else *)
                          )), ltac:(M.monadic (
                            M.pure Constant.None_
                          )) |) in
                        let _ :=
                          (* if *)
                          M.if_then_else (|
                            Compare.eq (|
                              M.get_subscript (|
                                M.get_name (| globals, locals_stack, "encoded_data" |),
                                Constant.int 1
                              |),
                              Constant.int 0
                            |),
                          (* then *)
                          ltac:(M.monadic (
                            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "RLPDecodingError" |)) |) in
                            M.pure Constant.None_
                          (* else *)
                          )), ltac:(M.monadic (
                            M.pure Constant.None_
                          )) |) in
                        let _ := M.assign_local (|
                          "decoded_data_length" ,
                          M.call (|
                            M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
                            make_list [
                              M.slice (|
                                M.get_name (| globals, locals_stack, "encoded_data" |),
                                Constant.int 1,
                                BinOp.add (|
                                  Constant.int 1,
                                  M.get_name (| globals, locals_stack, "length_length" |)
                                |),
                                Constant.None_
                              |)
                            ],
                            make_dict []
                          |)
                        |) in
                        M.pure Constant.None_
                      (* else *)
                      )), ltac:(M.monadic (
                        M.pure Constant.None_
                      )) |) in
                    M.pure Constant.None_
                  )) |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      BinOp.add (|
        BinOp.add (|
          Constant.int 1,
          M.get_name (| globals, locals_stack, "length_length" |)
        |),
        M.get_name (| globals, locals_stack, "decoded_data_length" |)
      |)
    |) in
    M.pure Constant.None_)).

Axiom decode_item_length_in_globals :
  IsInGlobals globals "decode_item_length" (make_function decode_item_length).

Definition rlp_hash : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "data" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Obtain the keccak-256 hash of the rlp encoding of the passed in data.

    Parameters
    ----------
    data :
        The data for which we need the rlp hash.

    Returns
    -------
    hash : `Hash32`
        The rlp hash of the passed in data.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "encode" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom rlp_hash_in_globals :
  IsInGlobals globals "rlp_hash" (make_function rlp_hash).
