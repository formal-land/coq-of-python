Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.muir_glacier.utils.message".

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

Message specific functions used in this muir_glacier version of
specification.
".

Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_muir_glacier_fork_types_imports_Address :
  IsImported globals "ethereum.muir_glacier.fork_types" "Address".

Axiom ethereum_muir_glacier_state_imports_get_account :
  IsImported globals "ethereum.muir_glacier.state" "get_account".

Axiom ethereum_muir_glacier_vm_imports_Environment :
  IsImported globals "ethereum.muir_glacier.vm" "Environment".
Axiom ethereum_muir_glacier_vm_imports_Message :
  IsImported globals "ethereum.muir_glacier.vm" "Message".

Axiom ethereum_muir_glacier_utils_address_imports_compute_contract_address :
  IsImported globals "ethereum.muir_glacier.utils.address" "compute_contract_address".

Definition prepare_message : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "caller"; "target"; "value"; "data"; "gas"; "env"; "code_address"; "should_transfer_value"; "is_static" ] in
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

    Returns
    -------
    message: `ethereum.muir_glacier.vm.Message`
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
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Message" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom prepare_message_in_globals :
  IsInGlobals globals "prepare_message" (make_function prepare_message).
