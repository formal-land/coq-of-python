Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Utility Functions For Hexadecimal Strings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Hexadecimal utility functions used in this specification, specific to
Arrow Glacier types.
".

Require ethereum.utils.hexadecimal.
Axiom ethereum_utils_hexadecimal_remove_hex_prefix :
  IsGlobalAlias globals ethereum.utils.hexadecimal.globals "remove_hex_prefix".

Require fork_types.
Axiom fork_types_Address :
  IsGlobalAlias globals fork_types.globals "Address".
Axiom fork_types_Bloom :
  IsGlobalAlias globals fork_types.globals "Bloom".
Axiom fork_types_Root :
  IsGlobalAlias globals fork_types.globals "Root".

Definition hex_to_root : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "hex_string" ] |) in
    let _ := Constant.str "
    Convert hex string to trie root.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to trie root.

    Returns
    -------
    root : `Root`
        Trie root obtained from the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Root" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "bytes" |), "fromhex" |),
            make_list [
              M.call (|
                M.get_name (| globals, "remove_hex_prefix" |),
                make_list [
                  M.get_name (| globals, "hex_string" |)
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

Definition hex_to_bloom : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "hex_string" ] |) in
    let _ := Constant.str "
    Convert hex string to bloom.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to bloom.

    Returns
    -------
    bloom : `Bloom`
        Bloom obtained from the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Bloom" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "bytes" |), "fromhex" |),
            make_list [
              M.call (|
                M.get_name (| globals, "remove_hex_prefix" |),
                make_list [
                  M.get_name (| globals, "hex_string" |)
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

Definition hex_to_address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "hex_string" ] |) in
    let _ := Constant.str "
    Convert hex string to Address (20 bytes).

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to Address.

    Returns
    -------
    address : `Address`
        The address obtained from the given hexadecimal string.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Address" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "bytes" |), "fromhex" |),
            make_list [
              M.call (|
                M.get_field (| M.call (|
                  M.get_name (| globals, "remove_hex_prefix" |),
                  make_list [
                    M.get_name (| globals, "hex_string" |)
                  ],
                  make_dict []
                |), "rjust" |),
                make_list [
                  Constant.int 40;
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
