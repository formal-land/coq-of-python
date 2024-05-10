Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.crypto.hash".

Definition expr_1 : Value.t :=
  Constant.str "
Cryptographic Hash Functions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Cryptographic hashing functions.
".

Axiom Crypto_Hash_imports_keccak :
  IsImported globals "Crypto.Hash" "keccak".

Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes32 :
  IsImported globals "ethereum.base_types" "Bytes32".
Axiom ethereum_base_types_imports_Bytes64 :
  IsImported globals "ethereum.base_types" "Bytes64".

Definition Hash32 : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, "Bytes32" |)
)).

Definition Hash64 : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, "Bytes64" |)
)).

Definition keccak256 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "buffer" ] |) in
    let _ := Constant.str "
    Computes the keccak256 hash of the input `buffer`.

    Parameters
    ----------
    buffer :
        Input for the hashing function.

    Returns
    -------
    hash : `ethereum.base_types.Hash32`
        Output of the hash function.
    " in
    let _ := M.assign_local (|
      "k" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "keccak" |), "new" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Hash32" |),
        make_list [
          M.call (|
            M.get_field (| M.call (|
              M.get_field (| M.get_name (| globals, "k" |), "update" |),
              make_list [
                M.get_name (| globals, "buffer" |)
              ],
              make_dict []
            |), "digest" |),
            make_list [],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition keccak512 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "buffer" ] |) in
    let _ := Constant.str "
    Computes the keccak512 hash of the input `buffer`.

    Parameters
    ----------
    buffer :
        Input for the hashing function.

    Returns
    -------
    hash : `ethereum.base_types.Hash32`
        Output of the hash function.
    " in
    let _ := M.assign_local (|
      "k" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "keccak" |), "new" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Hash64" |),
        make_list [
          M.call (|
            M.get_field (| M.call (|
              M.get_field (| M.get_name (| globals, "k" |), "update" |),
              make_list [
                M.get_name (| globals, "buffer" |)
              ],
              make_dict []
            |), "digest" |),
            make_list [],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
