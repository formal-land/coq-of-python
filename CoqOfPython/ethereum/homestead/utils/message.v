Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Hardfork Utility Functions For The Message Data-structure
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Message specific functions used in this homestead version of specification.
".

Require typing.
Axiom typing_Optional :
  IsGlobalAlias globals typing.globals "Optional".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".
Axiom ethereum_base_types_Bytes0 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes0".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require fork_types.
Axiom fork_types_Address :
  IsGlobalAlias globals fork_types.globals "Address".

Require state.
Axiom state_get_account :
  IsGlobalAlias globals state.globals "get_account".

Require vm.
Axiom vm_Environment :
  IsGlobalAlias globals vm.globals "Environment".
Axiom vm_Message :
  IsGlobalAlias globals vm.globals "Message".

Require address.
Axiom address_compute_contract_address :
  IsGlobalAlias globals address.globals "compute_contract_address".

Definition prepare_message : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "caller"; "target"; "value"; "data"; "gas"; "env"; "code_address"; "should_transfer_value" ] |) in
    let _ := Constant.str "
    Execute a transaction against the provided environment.

    Parameters
    ----------
    caller :
        Address which initiated the transaction
    target :
        Address whose code will be executed
    value :
        Value to be transferred.
    data :
        Array of bytes provided to the code in `target`.
    gas :
        Gas provided for the code in `target`.
    env :
        Environment for the Ethereum Virtual Machine.
    code_address :
        This is usually same as the `target` address except when an alternative
        accounts code needs to be executed.
        eg. `CALLCODE` calling a precompile.
    should_transfer_value :
        if True ETH should be transferred while executing a message call.

    Returns
    -------
    message: `ethereum.homestead.vm.Message`
        Items containing contract creation or message call specific data.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "isinstance" |),
          make_list [
            M.get_name (| globals, "target" |);
            M.get_name (| globals, "Bytes0" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let current_target :=
          M.call (|
            M.get_name (| globals, "compute_contract_address" |),
            make_list [
              M.get_name (| globals, "caller" |);
              BinOp.sub (|
                M.get_field (| M.call (|
                  M.get_name (| globals, "get_account" |),
                  make_list [
                    M.get_field (| M.get_name (| globals, "env" |), "state" |);
                    M.get_name (| globals, "caller" |)
                  ],
                  make_dict []
                |), "nonce" |),
                M.call (|
                  M.get_name (| globals, "U256" |),
                  make_list [
                    Constant.int 1
                  ],
                  make_dict []
                |)
              |)
            ],
            make_dict []
          |) in
        let msg_data :=
          M.call (|
            M.get_name (| globals, "Bytes" |),
            make_list [
              (* At constant: unsupported node type: Constant *)
            ],
            make_dict []
          |) in
        let code :=
          M.get_name (| globals, "data" |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, "isinstance" |),
              make_list [
                M.get_name (| globals, "target" |);
                M.get_name (| globals, "Address" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let current_target :=
              M.get_name (| globals, "target" |) in
            let msg_data :=
              M.get_name (| globals, "data" |) in
            let code :=
              M.get_field (| M.call (|
                M.get_name (| globals, "get_account" |),
                make_list [
                  M.get_field (| M.get_name (| globals, "env" |), "state" |);
                  M.get_name (| globals, "target" |)
                ],
                make_dict []
              |), "code" |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.is (| M.get_name (| globals, "code_address" |), Constant.None_ |),
              (* then *)
              ltac:(M.monadic (
                let code_address :=
                  M.get_name (| globals, "target" |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.raise (| M.call (|
              M.get_name (| globals, "AssertionError" |),
              make_list [
                Constant.str "Target must be address or empty bytes"
              ],
              make_dict []
            |) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Message" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
