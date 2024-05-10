Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Precompiled Contract Addresses
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Addresses of precompiled contracts and mappings to their
implementations.
".

Require ethereum.dao_fork.utils.hexadecimal.
Axiom ethereum_dao_fork_utils_hexadecimal_hex_to_address :
  IsGlobalAlias globals ethereum.dao_fork.utils.hexadecimal.globals "hex_to_address".

Definition __all__ : Value.t := M.run ltac:(M.monadic (
  make_tuple [ Constant.str "ECRECOVER_ADDRESS"; Constant.str "SHA256_ADDRESS"; Constant.str "RIPEMD160_ADDRESS"; Constant.str "IDENTITY_ADDRESS" ]
)).

Definition ECRECOVER_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "hex_to_address" |),
    make_list [
      Constant.str "0x01"
    ],
    make_dict []
  |)
)).

Definition SHA256_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "hex_to_address" |),
    make_list [
      Constant.str "0x02"
    ],
    make_dict []
  |)
)).

Definition RIPEMD160_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "hex_to_address" |),
    make_list [
      Constant.str "0x03"
    ],
    make_dict []
  |)
)).

Definition IDENTITY_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "hex_to_address" |),
    make_list [
      Constant.str "0x04"
    ],
    make_dict []
  |)
)).
