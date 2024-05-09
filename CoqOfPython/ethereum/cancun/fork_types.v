Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require __init__.
Axiom __init___rlp :
  IsGlobalAlias globals __init__.globals "rlp".

Require base_types.
Axiom base_types_U256 :
  IsGlobalAlias globals base_types.globals "U256".
Axiom base_types_Bytes :
  IsGlobalAlias globals base_types.globals "Bytes".
Axiom base_types_Bytes20 :
  IsGlobalAlias globals base_types.globals "Bytes20".
Axiom base_types_Bytes256 :
  IsGlobalAlias globals base_types.globals "Bytes256".
Axiom base_types_Uint :
  IsGlobalAlias globals base_types.globals "Uint".
Axiom base_types_slotted_freezable :
  IsGlobalAlias globals base_types.globals "slotted_freezable".

Require crypto.hash.
Axiom crypto_hash_Hash32 :
  IsGlobalAlias globals crypto.hash.globals "Hash32".
Axiom crypto_hash_keccak256 :
  IsGlobalAlias globals crypto.hash.globals "keccak256".

Definition Address : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, "Bytes20" |)
)).

Definition Root : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, "Hash32" |)
)).

Definition VersionedHash : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, "Hash32" |)
)).

Definition Bloom : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, "Bytes256" |)
)).

Definition Account : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition EMPTY_ACCOUNT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Account" |),
    make_list [],
    make_dict []
  |)
)).

Definition encode_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "raw_account_data"; "storage_root" ] |) in
    let _ := Constant.str "
    Encode `Account` dataclass.

    Storage is not stored in the `Account` dataclass, so `Accounts` cannot be
    encoded with providing a storage root.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
        make_list [
          make_tuple [ M.get_field (| M.get_name (| globals, "raw_account_data" |), "nonce" |); M.get_field (| M.get_name (| globals, "raw_account_data" |), "balance" |); M.get_name (| globals, "storage_root" |); M.call (|
            M.get_name (| globals, "keccak256" |),
            make_list [
              M.get_field (| M.get_name (| globals, "raw_account_data" |), "code" |)
            ],
            make_dict []
          |) ]
        ],
        make_dict []
      |)
    M.pure Constant.None_)).
