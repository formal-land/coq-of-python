Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.shanghai.utils.message".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Hardfork Utility Functions For The Message Data-structure
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Message specific functions used in this shanghai version of
specification.
".

Axiom typing_imports_FrozenSet :
  IsImported globals "typing" "FrozenSet".
Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".
Axiom ethereum_base_types_imports_Bytes32 :
  IsImported globals "ethereum.base_types" "Bytes32".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_shanghai_fork_types_imports_Address :
  IsImported globals "ethereum.shanghai.fork_types" "Address".

Axiom ethereum_shanghai_state_imports_get_account :
  IsImported globals "ethereum.shanghai.state" "get_account".

Axiom ethereum_shanghai_vm_imports_Environment :
  IsImported globals "ethereum.shanghai.vm" "Environment".
Axiom ethereum_shanghai_vm_imports_Message :
  IsImported globals "ethereum.shanghai.vm" "Message".

Axiom ethereum_shanghai_vm_precompiled_contracts_mapping_imports_PRE_COMPILED_CONTRACTS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.mapping" "PRE_COMPILED_CONTRACTS".

Axiom ethereum_shanghai_utils_address_imports_compute_contract_address :
  IsImported globals "ethereum.shanghai.utils.address" "compute_contract_address".

Definition prepare_message : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "caller"; "target"; "value"; "data"; "gas"; "env"; "code_address"; "should_transfer_value"; "is_static"; "preaccessed_addresses"; "preaccessed_storage_keys" ] in
    ltac:(M.monadic (
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
    is_static:
        if True then it prevents all state-changing operations from being
        executed.
    preaccessed_addresses:
        Addresses that should be marked as accessed prior to the message call
    preaccessed_storage_keys:
        Storage keys that should be marked as accessed prior to the message
        call

    Returns
    -------
    message: `ethereum.shanghai.vm.Message`
        Items containing contract creation or message call specific data.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "target" |);
            M.get_name (| globals, locals_stack, "Bytes0" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "current_target" ,
          M.call (|
            M.get_name (| globals, locals_stack, "compute_contract_address" |),
            make_list [
              M.get_name (| globals, locals_stack, "caller" |);
              BinOp.sub (|
                M.get_field (| M.call (|
                  M.get_name (| globals, locals_stack, "get_account" |),
                  make_list [
                    M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
                    M.get_name (| globals, locals_stack, "caller" |)
                  ],
                  make_dict []
                |), "nonce" |),
                M.call (|
                  M.get_name (| globals, locals_stack, "U256" |),
                  make_list [
                    Constant.int 1
                  ],
                  make_dict []
                |)
              |)
            ],
            make_dict []
          |)
        |) in
        let _ := M.assign_local (|
          "msg_data" ,
          M.call (|
            M.get_name (| globals, locals_stack, "Bytes" |),
            make_list [
              Constant.bytes ""
            ],
            make_dict []
          |)
        |) in
        let _ := M.assign_local (|
          "code" ,
          M.get_name (| globals, locals_stack, "data" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, locals_stack, "isinstance" |),
              make_list [
                M.get_name (| globals, locals_stack, "target" |);
                M.get_name (| globals, locals_stack, "Address" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "current_target" ,
              M.get_name (| globals, locals_stack, "target" |)
            |) in
            let _ := M.assign_local (|
              "msg_data" ,
              M.get_name (| globals, locals_stack, "data" |)
            |) in
            let _ := M.assign_local (|
              "code" ,
              M.get_field (| M.call (|
                M.get_name (| globals, locals_stack, "get_account" |),
                make_list [
                  M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
                  M.get_name (| globals, locals_stack, "target" |)
                ],
                make_dict []
              |), "code" |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.is (|
                  M.get_name (| globals, locals_stack, "code_address" |),
                  Constant.None_
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.assign_local (|
                  "code_address" ,
                  M.get_name (| globals, locals_stack, "target" |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.raise (| Some (M.call (|
              M.get_name (| globals, locals_stack, "AssertionError" |),
              make_list [
                Constant.str "Target must be address or empty bytes"
              ],
              make_dict []
            |)) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "accessed_addresses" ,
      M.call (|
        M.get_name (| globals, locals_stack, "set" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "accessed_addresses" |), "add" |),
    make_list [
      M.get_name (| globals, locals_stack, "current_target" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "accessed_addresses" |), "add" |),
    make_list [
      M.get_name (| globals, locals_stack, "caller" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "accessed_addresses" |), "update" |),
    make_list [
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "PRE_COMPILED_CONTRACTS" |), "keys" |),
        make_list [],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "accessed_addresses" |), "update" |),
    make_list [
      M.get_name (| globals, locals_stack, "preaccessed_addresses" |)
    ],
    make_dict []
  |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Message" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
