Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.utils.hexadecimal".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Utility Functions For Hexadecimal Strings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Hexadecimal strings specific utility functions used in this specification.
".

Axiom ethereum_base_types_imports_U64 :
  IsImported globals "ethereum.base_types" "U64".
Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes8 :
  IsImported globals "ethereum.base_types" "Bytes8".
Axiom ethereum_base_types_imports_Bytes20 :
  IsImported globals "ethereum.base_types" "Bytes20".
Axiom ethereum_base_types_imports_Bytes32 :
  IsImported globals "ethereum.base_types" "Bytes32".
Axiom ethereum_base_types_imports_Bytes256 :
  IsImported globals "ethereum.base_types" "Bytes256".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_crypto_hash_imports_Hash32 :
  IsImported globals "ethereum.crypto.hash" "Hash32".

Definition has_hex_prefix : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Check if a hex string starts with hex prefix (0x).

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be checked for presence of prefix.

    Returns
    -------
    has_prefix : `bool`
        Boolean indicating whether the hex string has 0x prefix.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "hex_string" |), "startswith" |),
        make_list [
          Constant.str "0x"
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom has_hex_prefix_in_globals :
  IsInGlobals globals "has_hex_prefix" (make_function has_hex_prefix).

Definition remove_hex_prefix : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Remove 0x prefix from a hex string if present. This function returns the
    passed hex string if it isn't prefixed with 0x.

    Parameters
    ----------
    hex_string :
        The hexadecimal string whose prefix is to be removed.

    Returns
    -------
    modified_hex_string : `str`
        The hexadecimal string with the 0x prefix removed if present.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "has_hex_prefix" |),
          make_list [
            M.get_name (| globals, locals_stack, "hex_string" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.slice (|
            M.get_name (| globals, locals_stack, "hex_string" |),
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                Constant.str "0x"
              ],
              make_dict []
            |),
            Constant.None_,
            Constant.None_
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "hex_string" |)
    |) in
    M.pure Constant.None_)).

Axiom remove_hex_prefix_in_globals :
  IsInGlobals globals "remove_hex_prefix" (make_function remove_hex_prefix).

Definition hex_to_bytes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to bytes.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to bytes.

    Returns
    -------
    byte_stream : `bytes`
        Byte stream corresponding to the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "bytes" |), "fromhex" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
            make_list [
              M.get_name (| globals, locals_stack, "hex_string" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom hex_to_bytes_in_globals :
  IsInGlobals globals "hex_to_bytes" (make_function hex_to_bytes).

Definition hex_to_bytes8 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to 8 bytes.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to 8 bytes.

    Returns
    -------
    8_byte_stream : `Bytes8`
        8-byte stream corresponding to the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Bytes8" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "bytes" |), "fromhex" |),
            make_list [
              M.call (|
                M.get_field (| M.call (|
                  M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "hex_string" |)
                  ],
                  make_dict []
                |), "rjust" |),
                make_list [
                  Constant.int 16;
                  Constant.str "0"
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
    M.pure Constant.None_)).

Axiom hex_to_bytes8_in_globals :
  IsInGlobals globals "hex_to_bytes8" (make_function hex_to_bytes8).

Definition hex_to_bytes20 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to 20 bytes.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to 20 bytes.

    Returns
    -------
    20_byte_stream : `Bytes20`
        20-byte stream corresponding to the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Bytes20" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "bytes" |), "fromhex" |),
            make_list [
              M.call (|
                M.get_field (| M.call (|
                  M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "hex_string" |)
                  ],
                  make_dict []
                |), "rjust" |),
                make_list [
                  Constant.int 20;
                  Constant.str "0"
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
    M.pure Constant.None_)).

Axiom hex_to_bytes20_in_globals :
  IsInGlobals globals "hex_to_bytes20" (make_function hex_to_bytes20).

Definition hex_to_bytes32 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to 32 bytes.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to 32 bytes.

    Returns
    -------
    32_byte_stream : `Bytes32`
        32-byte stream corresponding to the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Bytes32" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "bytes" |), "fromhex" |),
            make_list [
              M.call (|
                M.get_field (| M.call (|
                  M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "hex_string" |)
                  ],
                  make_dict []
                |), "rjust" |),
                make_list [
                  Constant.int 64;
                  Constant.str "0"
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
    M.pure Constant.None_)).

Axiom hex_to_bytes32_in_globals :
  IsInGlobals globals "hex_to_bytes32" (make_function hex_to_bytes32).

Definition hex_to_bytes256 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to 256 bytes.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to 256 bytes.

    Returns
    -------
    256_byte_stream : `Bytes256`
        256-byte stream corresponding to the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Bytes256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "bytes" |), "fromhex" |),
            make_list [
              M.call (|
                M.get_field (| M.call (|
                  M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "hex_string" |)
                  ],
                  make_dict []
                |), "rjust" |),
                make_list [
                  Constant.int 512;
                  Constant.str "0"
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
    M.pure Constant.None_)).

Axiom hex_to_bytes256_in_globals :
  IsInGlobals globals "hex_to_bytes256" (make_function hex_to_bytes256).

Definition hex_to_hash : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to hash32 (32 bytes).

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to hash32.

    Returns
    -------
    hash : `Hash32`
        32-byte stream obtained from the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Hash32" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "bytes" |), "fromhex" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
                make_list [
                  M.get_name (| globals, locals_stack, "hex_string" |)
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
    M.pure Constant.None_)).

Axiom hex_to_hash_in_globals :
  IsInGlobals globals "hex_to_hash" (make_function hex_to_hash).

Definition hex_to_uint : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to Uint.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to Uint.

    Returns
    -------
    converted : `Uint`
        The unsigned integer obtained from the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "int" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
                make_list [
                  M.get_name (| globals, locals_stack, "hex_string" |)
                ],
                make_dict []
              |);
              Constant.int 16
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom hex_to_uint_in_globals :
  IsInGlobals globals "hex_to_uint" (make_function hex_to_uint).

Definition hex_to_u64 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to U64.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to U256.

    Returns
    -------
    converted : `U64`
        The U64 integer obtained from the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "U64" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "int" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
                make_list [
                  M.get_name (| globals, locals_stack, "hex_string" |)
                ],
                make_dict []
              |);
              Constant.int 16
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom hex_to_u64_in_globals :
  IsInGlobals globals "hex_to_u64" (make_function hex_to_u64).

Definition hex_to_u256 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Convert hex string to U256.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to U256.

    Returns
    -------
    converted : `U256`
        The U256 integer obtained from the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "int" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "remove_hex_prefix" |),
                make_list [
                  M.get_name (| globals, locals_stack, "hex_string" |)
                ],
                make_dict []
              |);
              Constant.int 16
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom hex_to_u256_in_globals :
  IsInGlobals globals "hex_to_u256" (make_function hex_to_u256).
