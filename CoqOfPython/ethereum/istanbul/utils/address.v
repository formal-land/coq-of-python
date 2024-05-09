Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Hardfork Utility Functions For Addresses
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Address specific functions used in this istanbul version of
specification.
".

Require typing.
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes32 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes32".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_keccak256 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak256".

Require ethereum.utils.byte.
Axiom ethereum_utils_byte_left_pad_zero_bytes :
  IsGlobalAlias globals ethereum.utils.byte.globals "left_pad_zero_bytes".

Require __init__.
Axiom __init___rlp :
  IsGlobalAlias globals __init__.globals "rlp".

Require fork_types.
Axiom fork_types_Address :
  IsGlobalAlias globals fork_types.globals "Address".

Definition to_address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "data" ] |) in
    let _ := Constant.str "
    Convert a Uint or U256 value to a valid address (20 bytes).

    Parameters
    ----------
    data :
        The string to be converted to bytes.

    Returns
    -------
    address : `Address`
        The obtained address.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Address" |),
        make_list [
          M.get_subscript (| M.call (|
            M.get_field (| M.get_name (| globals, "data" |), "to_be_bytes32" |),
            make_list [],
            make_dict []
          |), UnOp.sub (| Constant.int 20 |):(* At expr: unsupported node type: NoneType *) |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition compute_contract_address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "address"; "nonce" ] |) in
    let _ := Constant.str "
    Computes address of the new account that needs to be created.

    Parameters
    ----------
    address :
        The address of the account that wants to create the new account.
    nonce :
        The transaction count of the account that wants to create the new
        account.

    Returns
    -------
    address: `Address`
        The computed address of the new account.
    " in
    let computed_address :=
      M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
            make_list [
              make_list [
                M.get_name (| globals, "address" |);
                M.get_name (| globals, "nonce" |)
              ]
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let canonical_address :=
      M.get_subscript (| M.get_name (| globals, "computed_address" |), UnOp.sub (| Constant.int 20 |):(* At expr: unsupported node type: NoneType *) |) in
    let padded_address :=
      M.call (|
        M.get_name (| globals, "left_pad_zero_bytes" |),
        make_list [
          M.get_name (| globals, "canonical_address" |);
          Constant.int 20
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Address" |),
        make_list [
          M.get_name (| globals, "padded_address" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition compute_create2_contract_address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "address"; "salt"; "call_data" ] |) in
    let _ := Constant.str "
    Computes address of the new account that needs to be created, which is
    based on the sender address, salt and the call data as well.

    Parameters
    ----------
    address :
        The address of the account that wants to create the new account.
    salt :
        Address generation salt.
    call_data :
        The code of the new account which is to be created.

    Returns
    -------
    address: `ethereum.istanbul.fork_types.Address`
        The computed address of the new account.
    " in
    let preimage :=
      BinOp.add (|
        BinOp.add (|
          BinOp.add (|
            (* At constant: unsupported node type: Constant *),
            M.get_name (| globals, "address" |)
          |),
          M.get_name (| globals, "salt" |)
        |),
        M.call (|
          M.get_name (| globals, "keccak256" |),
          make_list [
            M.get_name (| globals, "call_data" |)
          ],
          make_dict []
        |)
      |) in
    let computed_address :=
      M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.get_name (| globals, "preimage" |)
        ],
        make_dict []
      |) in
    let canonical_address :=
      M.get_subscript (| M.get_name (| globals, "computed_address" |), UnOp.sub (| Constant.int 20 |):(* At expr: unsupported node type: NoneType *) |) in
    let padded_address :=
      M.call (|
        M.get_name (| globals, "left_pad_zero_bytes" |),
        make_list [
          M.get_name (| globals, "canonical_address" |);
          Constant.int 20
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Address" |),
        make_list [
          M.get_name (| globals, "padded_address" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
