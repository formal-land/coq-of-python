Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require dataclasses.
Axiom dataclasses_astuple :
  IsGlobalAlias globals dataclasses.globals "astuple".
Axiom dataclasses_fields :
  IsGlobalAlias globals dataclasses.globals "fields".
Axiom dataclasses_is_dataclass :
  IsGlobalAlias globals dataclasses.globals "is_dataclass".

Require typing.
Axiom typing_Any :
  IsGlobalAlias globals typing.globals "Any".
Axiom typing_List :
  IsGlobalAlias globals typing.globals "List".
Axiom typing_Sequence :
  IsGlobalAlias globals typing.globals "Sequence".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".
Axiom typing_Type_ :
  IsGlobalAlias globals typing.globals "Type_".
Axiom typing_TypeVar :
  IsGlobalAlias globals typing.globals "TypeVar".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".
Axiom typing_cast :
  IsGlobalAlias globals typing.globals "cast".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_Hash32 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "Hash32".
Axiom ethereum_crypto_hash_keccak256 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak256".

Require ethereum.exceptions.
Axiom ethereum_exceptions_RLPDecodingError :
  IsGlobalAlias globals ethereum.exceptions.globals "RLPDecodingError".
Axiom ethereum_exceptions_RLPEncodingError :
  IsGlobalAlias globals ethereum.exceptions.globals "RLPEncodingError".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require base_types.
Axiom base_types_Bytes :
  IsGlobalAlias globals base_types.globals "Bytes".
Axiom base_types_Bytes0 :
  IsGlobalAlias globals base_types.globals "Bytes0".
Axiom base_types_Bytes20 :
  IsGlobalAlias globals base_types.globals "Bytes20".
Axiom base_types_FixedBytes :
  IsGlobalAlias globals base_types.globals "FixedBytes".
Axiom base_types_FixedUint :
  IsGlobalAlias globals base_types.globals "FixedUint".
Axiom base_types_Uint :
  IsGlobalAlias globals base_types.globals "Uint".

Definition RLP : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, "Any" |)
)).

Definition encode : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "raw_data" ] |) in
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
        let _ :=
            let _ :=
                let _ :=
                    let _ :=
                        let _ :=
                            let _ := M.raise (| Some(M.call (|
                              M.get_name (| globals, "RLPEncodingError" |),
                              make_list [
                                M.call (|
                                  M.get_field (| Constant.str "RLP Encoding of type {} is not supported", "format" |),
                                  make_list [
                                    M.call (|
                                      M.get_name (| globals, "type" |),
                                      make_list [
                                        M.get_name (| globals, "raw_data" |)
                                      ],
                                      make_dict []
                                    |)
                                  ],
                                  make_dict []
                                |)
                              ],
                              make_dict []
                            |))
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

Definition encode_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "raw_bytes" ] |) in
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
    let len_raw_data :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "raw_bytes" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ :=
        let _ :=
            let len_raw_data_as_be :=
              M.call (|
                M.get_field (| M.get_name (| globals, "len_raw_data" |), "to_be_bytes" |),
                make_list [],
                make_dict []
              |) in
            let _ := M.return_ (|
              BinOp.add (|
                BinOp.add (|
                  M.call (|
                    M.get_name (| globals, "bytes" |),
                    make_list [
                      make_list [
                        BinOp.add (|
                          Constant.int 183,
                          M.call (|
                            M.get_name (| globals, "len" |),
                            make_list [
                              M.get_name (| globals, "len_raw_data_as_be" |)
                            ],
                            make_dict []
                          |)
                        |)
                      ]
                    ],
                    make_dict []
                  |),
                  M.get_name (| globals, "len_raw_data_as_be" |)
                |),
                M.get_name (| globals, "raw_bytes" |)
              |)
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition encode_sequence : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "raw_sequence" ] |) in
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
    let joined_encodings :=
      M.call (|
        M.get_name (| globals, "get_joined_encodings" |),
        make_list [
          M.get_name (| globals, "raw_sequence" |)
        ],
        make_dict []
      |) in
    let len_joined_encodings :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "joined_encodings" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ :=
        let len_joined_encodings_as_be :=
          M.call (|
            M.get_field (| M.get_name (| globals, "len_joined_encodings" |), "to_be_bytes" |),
            make_list [],
            make_dict []
          |) in
        let _ := M.return_ (|
          BinOp.add (|
            BinOp.add (|
              M.call (|
                M.get_name (| globals, "Bytes" |),
                make_list [
                  make_list [
                    BinOp.add (|
                      Constant.int 247,
                      M.call (|
                        M.get_name (| globals, "len" |),
                        make_list [
                          M.get_name (| globals, "len_joined_encodings_as_be" |)
                        ],
                        make_dict []
                      |)
                    |)
                  ]
                ],
                make_dict []
              |),
              M.get_name (| globals, "len_joined_encodings_as_be" |)
            |),
            M.get_name (| globals, "joined_encodings" |)
          |)
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition get_joined_encodings : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "raw_sequence" ] |) in
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
          (* At expr: unsupported node type: GeneratorExp *)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition decode : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "encoded_data" ] |) in
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
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt (|
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "encoded_data" |)
          ],
          make_dict []
        |),
        Constant.int 0
      |);
      M.call (|
        M.get_name (| globals, "RLPDecodingError" |),
        make_list [
          Constant.str "Cannot decode empty bytestring"
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ :=
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "decode_to_sequence" |),
            make_list [
              M.get_name (| globals, "encoded_data" |)
            ],
            make_dict []
          |)
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition T : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
    make_list [
      Constant.str "T"
    ],
    make_dict []
  |)
)).

Definition decode_to : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "cls"; "encoded_data" ] |) in
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
        M.get_name (| globals, "_decode_to" |),
        make_list [
          M.get_name (| globals, "cls" |);
          M.call (|
            M.get_name (| globals, "decode" |),
            make_list [
              M.get_name (| globals, "encoded_data" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition _decode_to : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "cls"; "raw_rlp" ] |) in
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
        let _ :=
            let _ :=
                let _ :=
                    let _ :=
                        let _ :=
                            let _ :=
                                let _ :=
                                    let _ :=
                                        let _ := M.raise (| Some(M.call (|
                                          M.get_name (| globals, "RLPDecodingError" |),
                                          make_list [
                                            M.call (|
                                              M.get_field (| Constant.str "RLP Decoding to type {} is not supported", "format" |),
                                              make_list [
                                                M.get_name (| globals, "cls" |)
                                              ],
                                              make_dict []
                                            |)
                                          ],
                                          make_dict []
                                        |))
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

Definition decode_to_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "encoded_bytes" ] |) in
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
        let _ :=
            let decoded_data_start_idx :=
              BinOp.sub (|
                BinOp.add (|
                  Constant.int 1,
                  M.get_subscript (| M.get_name (| globals, "encoded_bytes" |), Constant.int 0 |)
                |),
                Constant.int 183
              |) in
            let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt (|
        BinOp.sub (|
          M.get_name (| globals, "decoded_data_start_idx" |),
          Constant.int 1
        |),
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "encoded_bytes" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
            let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.not_eq (|
        M.get_subscript (| M.get_name (| globals, "encoded_bytes" |), Constant.int 1 |),
        Constant.int 0
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
            let len_decoded_data :=
              M.call (|
                M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
                make_list [
                  M.get_subscript (| M.get_name (| globals, "encoded_bytes" |), Constant.int 1 |)
                ],
                make_dict []
              |) in
            let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt_e (|
        M.get_name (| globals, "len_decoded_data" |),
        Constant.int 56
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
            let decoded_data_end_idx :=
              BinOp.add (|
                M.get_name (| globals, "decoded_data_start_idx" |),
                M.get_name (| globals, "len_decoded_data" |)
              |) in
            let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt (|
        BinOp.sub (|
          M.get_name (| globals, "decoded_data_end_idx" |),
          Constant.int 1
        |),
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "encoded_bytes" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
            let _ := M.return_ (|
              M.get_subscript (| M.get_name (| globals, "encoded_bytes" |), M.get_name (| globals, "decoded_data_start_idx" |) |)
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition decode_to_sequence : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "encoded_sequence" ] |) in
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
        let joined_encodings_start_idx :=
          BinOp.sub (|
            BinOp.add (|
              Constant.int 1,
              M.get_subscript (| M.get_name (| globals, "encoded_sequence" |), Constant.int 0 |)
            |),
            Constant.int 247
          |) in
        let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt (|
        BinOp.sub (|
          M.get_name (| globals, "joined_encodings_start_idx" |),
          Constant.int 1
        |),
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "encoded_sequence" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
        let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.not_eq (|
        M.get_subscript (| M.get_name (| globals, "encoded_sequence" |), Constant.int 1 |),
        Constant.int 0
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
        let len_joined_encodings :=
          M.call (|
            M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
            make_list [
              M.get_subscript (| M.get_name (| globals, "encoded_sequence" |), Constant.int 1 |)
            ],
            make_dict []
          |) in
        let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt_e (|
        M.get_name (| globals, "len_joined_encodings" |),
        Constant.int 56
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
        let joined_encodings_end_idx :=
          BinOp.add (|
            M.get_name (| globals, "joined_encodings_start_idx" |),
            M.get_name (| globals, "len_joined_encodings" |)
          |) in
        let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt (|
        BinOp.sub (|
          M.get_name (| globals, "joined_encodings_end_idx" |),
          Constant.int 1
        |),
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "encoded_sequence" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
        let joined_encodings :=
          M.get_subscript (| M.get_name (| globals, "encoded_sequence" |), M.get_name (| globals, "joined_encodings_start_idx" |) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "decode_joined_encodings" |),
        make_list [
          M.get_name (| globals, "joined_encodings" |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition decode_joined_encodings : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "joined_encodings" ] |) in
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
    let decoded_sequence :=
      make_list [] in
    let item_start_idx :=
      Constant.int 0 in
    While Compare.lt (|
    M.get_name (| globals, "item_start_idx" |),
    M.call (|
      M.get_name (| globals, "len" |),
      make_list [
        M.get_name (| globals, "joined_encodings" |)
      ],
      make_dict []
    |)
  |) do
      let encoded_item_length :=
        M.call (|
          M.get_name (| globals, "decode_item_length" |),
          make_list [
            M.get_subscript (| M.get_name (| globals, "joined_encodings" |), M.get_name (| globals, "item_start_idx" |) |)
          ],
          make_dict []
        |) in
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt (|
        BinOp.sub (|
          BinOp.add (|
            M.get_name (| globals, "item_start_idx" |),
            M.get_name (| globals, "encoded_item_length" |)
          |),
          Constant.int 1
        |),
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "joined_encodings" |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
      let encoded_item :=
        M.get_subscript (| M.get_name (| globals, "joined_encodings" |), M.get_name (| globals, "item_start_idx" |) |) in
      let _ := M.call (|
    M.get_field (| M.get_name (| globals, "decoded_sequence" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, "decode" |),
        make_list [
          M.get_name (| globals, "encoded_item" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
      let item_start_idx := BinOp.add
        M.get_name (| globals, "encoded_item_length" |)
        M.get_name (| globals, "encoded_item_length" |) in
    EndWhile.
    let _ := M.return_ (|
      M.get_name (| globals, "decoded_sequence" |)
    M.pure Constant.None_)).

Definition decode_item_length : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "encoded_data" ] |) in
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
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt (|
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "encoded_data" |)
          ],
          make_dict []
        |),
        Constant.int 0
      |);
      M.get_name (| globals, "RLPDecodingError" |)
    ],
    make_dict []
  |) in
    let first_rlp_byte :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.get_subscript (| M.get_name (| globals, "encoded_data" |), Constant.int 0 |)
        ],
        make_dict []
      |) in
    let length_length :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |) in
    let decoded_data_length :=
      Constant.int 0 in
    let _ :=
        let _ :=
            let _ :=
                let _ :=
                    let _ :=
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
          M.get_name (| globals, "length_length" |)
        |),
        M.get_name (| globals, "decoded_data_length" |)
      |)
    M.pure Constant.None_)).

Definition rlp_hash : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "data" ] |) in
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
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.call (|
            M.get_name (| globals, "encode" |),
            make_list [
              M.get_name (| globals, "data" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).
