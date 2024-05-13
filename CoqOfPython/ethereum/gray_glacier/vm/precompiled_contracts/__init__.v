Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.gray_glacier.vm.precompiled_contracts.__init__".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_gray_glacier_utils_hexadecimal_imports_hex_to_address :
  IsImported globals "ethereum.gray_glacier.utils.hexadecimal" "hex_to_address".

Definition __all__ : Value.t := M.run ltac:(M.monadic (
  make_tuple [ Constant.str "ECRECOVER_ADDRESS"; Constant.str "SHA256_ADDRESS"; Constant.str "RIPEMD160_ADDRESS"; Constant.str "IDENTITY_ADDRESS"; Constant.str "MODEXP_ADDRESS"; Constant.str "ALT_BN128_ADD_ADDRESS"; Constant.str "ALT_BN128_MUL_ADDRESS"; Constant.str "ALT_BN128_PAIRING_CHECK_ADDRESS"; Constant.str "BLAKE2F_ADDRESS" ]
)).

Definition ECRECOVER_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x01"
    ],
    make_dict []
  |)
)).

Definition SHA256_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x02"
    ],
    make_dict []
  |)
)).

Definition RIPEMD160_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x03"
    ],
    make_dict []
  |)
)).

Definition IDENTITY_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x04"
    ],
    make_dict []
  |)
)).

Definition MODEXP_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x05"
    ],
    make_dict []
  |)
)).

Definition ALT_BN128_ADD_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x06"
    ],
    make_dict []
  |)
)).

Definition ALT_BN128_MUL_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x07"
    ],
    make_dict []
  |)
)).

Definition ALT_BN128_PAIRING_CHECK_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x08"
    ],
    make_dict []
  |)
)).

Definition BLAKE2F_ADDRESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0x09"
    ],
    make_dict []
  |)
)).
