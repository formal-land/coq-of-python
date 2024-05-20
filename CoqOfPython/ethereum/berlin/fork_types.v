Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.berlin.fork_types".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Types
^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Types re-used throughout the specification, which are specific to Ethereum.
".

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom ethereum_imports_rlp :
  IsImported globals "ethereum" "rlp".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes20 :
  IsImported globals "ethereum.base_types" "Bytes20".
Axiom ethereum_base_types_imports_Bytes256 :
  IsImported globals "ethereum.base_types" "Bytes256".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".
Axiom ethereum_base_types_imports_slotted_freezable :
  IsImported globals "ethereum.base_types" "slotted_freezable".

Axiom ethereum_crypto_hash_imports_Hash32 :
  IsImported globals "ethereum.crypto.hash" "Hash32".
Axiom ethereum_crypto_hash_imports_keccak256 :
  IsImported globals "ethereum.crypto.hash" "keccak256".

Definition Address : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, locals_stack, "Bytes20" |)
)).

Definition Root : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, locals_stack, "Hash32" |)
)).

Definition Bloom : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, locals_stack, "Bytes256" |)
)).

Definition Account : Value.t := make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition EMPTY_ACCOUNT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Account" |),
    make_list [],
    make_dict []
  |)
)).

Definition encode_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "raw_account_data"; "storage_root" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Encode `Account` dataclass.

    Storage is not stored in the `Account` dataclass, so `Accounts` cannot be
    encoded with providing a storage root.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
        make_list [
          make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "raw_account_data" |), "nonce" |); M.get_field (| M.get_name (| globals, locals_stack, "raw_account_data" |), "balance" |); M.get_name (| globals, locals_stack, "storage_root" |); M.call (|
            M.get_name (| globals, locals_stack, "keccak256" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "raw_account_data" |), "code" |)
            ],
            make_dict []
          |) ]
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom encode_account_in_globals :
  IsInGlobals globals "encode_account" (make_function encode_account).
