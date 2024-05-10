Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.frontier.utils.message".

Definition expr_1 : Value.t :=
  Constant.str "
Hardfork Utility Functions For The Message Data-structure
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Message specific functions used in this frontier version of specification.
".

Axiom typing_imports :
  AreImported globals "typing" [ "Optional"; "Union" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U256"; "Bytes"; "Bytes0"; "Uint" ].

Axiom ethereum_frontier_fork_types_imports :
  AreImported globals "ethereum.frontier.fork_types" [ "Address" ].

Axiom ethereum_frontier_state_imports :
  AreImported globals "ethereum.frontier.state" [ "get_account" ].

Axiom ethereum_frontier_vm_imports :
  AreImported globals "ethereum.frontier.vm" [ "Environment"; "Message" ].

Axiom ethereum_frontier_utils_address_imports :
  AreImported globals "ethereum.frontier.utils.address" [ "compute_contract_address" ].

Definition prepare_message : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "caller"; "target"; "value"; "data"; "gas"; "env"; "code_address" ] |) in
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

    Returns
    -------
    message: `ethereum.frontier.vm.Message`
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
              Constant.bytes ""
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
                Compare.is (|
                  M.get_name (| globals, "code_address" |),
                  Constant.None_
                |),
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
            let _ := M.raise (| Some (M.call (|
              M.get_name (| globals, "AssertionError" |),
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
        M.get_name (| globals, "Message" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
