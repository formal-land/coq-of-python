Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.london.utils.address".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Hardfork Utility Functions For Addresses
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Address specific functions used in this london version of
specification.
".

Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes32 :
  IsImported globals "ethereum.base_types" "Bytes32".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_crypto_hash_imports_keccak256 :
  IsImported globals "ethereum.crypto.hash" "keccak256".

Axiom ethereum_utils_byte_imports_left_pad_zero_bytes :
  IsImported globals "ethereum.utils.byte" "left_pad_zero_bytes".

Axiom ethereum_imports_rlp :
  IsImported globals "ethereum" "rlp".

Axiom ethereum_london_fork_types_imports_Address :
  IsImported globals "ethereum.london.fork_types" "Address".

Definition to_address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "data" ] in
    ltac:(M.monadic (
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
        M.get_name (| globals, locals_stack, "Address" |),
        make_list [
          M.slice (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "data" |), "to_be_bytes32" |),
              make_list [],
              make_dict []
            |),
            UnOp.sub (| Constant.int 20 |),
            Constant.None_,
            Constant.None_
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom to_address_in_globals :
  IsInGlobals globals "to_address" (make_function to_address).

Definition compute_contract_address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "address"; "nonce" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "computed_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
            make_list [
              make_list [
                M.get_name (| globals, locals_stack, "address" |);
                M.get_name (| globals, locals_stack, "nonce" |)
              ]
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "canonical_address" ,
      M.slice (|
        M.get_name (| globals, locals_stack, "computed_address" |),
        UnOp.sub (| Constant.int 20 |),
        Constant.None_,
        Constant.None_
      |)
    |) in
    let _ := M.assign_local (|
      "padded_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "left_pad_zero_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "canonical_address" |);
          Constant.int 20
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Address" |),
        make_list [
          M.get_name (| globals, locals_stack, "padded_address" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom compute_contract_address_in_globals :
  IsInGlobals globals "compute_contract_address" (make_function compute_contract_address).

Definition compute_create2_contract_address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "address"; "salt"; "call_data" ] in
    ltac:(M.monadic (
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
    address: `ethereum.london.fork_types.Address`
        The computed address of the new account.
    " in
    let _ := M.assign_local (|
      "preimage" ,
      BinOp.add (|
        BinOp.add (|
          BinOp.add (|
            Constant.bytes "ff",
            M.get_name (| globals, locals_stack, "address" |)
          |),
          M.get_name (| globals, locals_stack, "salt" |)
        |),
        M.call (|
          M.get_name (| globals, locals_stack, "keccak256" |),
          make_list [
            M.get_name (| globals, locals_stack, "call_data" |)
          ],
          make_dict []
        |)
      |)
    |) in
    let _ := M.assign_local (|
      "computed_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.get_name (| globals, locals_stack, "preimage" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "canonical_address" ,
      M.slice (|
        M.get_name (| globals, locals_stack, "computed_address" |),
        UnOp.sub (| Constant.int 20 |),
        Constant.None_,
        Constant.None_
      |)
    |) in
    let _ := M.assign_local (|
      "padded_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "left_pad_zero_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "canonical_address" |);
          Constant.int 20
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Address" |),
        make_list [
          M.get_name (| globals, locals_stack, "padded_address" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom compute_create2_contract_address_in_globals :
  IsInGlobals globals "compute_create2_contract_address" (make_function compute_create2_contract_address).
