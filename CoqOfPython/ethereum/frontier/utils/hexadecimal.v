Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.frontier.utils.hexadecimal".

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

Hexadecimal utility functions used in this specification, specific to Frontier
types.
".

Axiom ethereum_utils_hexadecimal_imports_remove_hex_prefix :
  IsImported globals "ethereum.utils.hexadecimal" "remove_hex_prefix".

Axiom ethereum_frontier_fork_types_imports_Address :
  IsImported globals "ethereum.frontier.fork_types" "Address".
Axiom ethereum_frontier_fork_types_imports_Bloom :
  IsImported globals "ethereum.frontier.fork_types" "Bloom".
Axiom ethereum_frontier_fork_types_imports_Root :
  IsImported globals "ethereum.frontier.fork_types" "Root".

Definition hex_to_root : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
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
        M.get_name (| globals, locals_stack, "Root" |),
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

Definition hex_to_bloom : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
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
        M.get_name (| globals, locals_stack, "Bloom" |),
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

Definition hex_to_address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hex_string" ] in
    ltac:(M.monadic (
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
        M.get_name (| globals, locals_stack, "Address" |),
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
