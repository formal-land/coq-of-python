Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Stack
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the stack operators for the EVM.
".

Require typing.
Axiom typing_List :
  IsGlobalAlias globals typing.globals "List".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".

Require ethereum.london.vm.exceptions.
Axiom ethereum_london_vm_exceptions_StackOverflowError :
  IsGlobalAlias globals ethereum.london.vm.exceptions.globals "StackOverflowError".
Axiom ethereum_london_vm_exceptions_StackUnderflowError :
  IsGlobalAlias globals ethereum.london.vm.exceptions.globals "StackUnderflowError".

Definition pop : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "stack" ] |) in
    let _ := Constant.str "
    Pops the top item off of `stack`.

    Parameters
    ----------
    stack :
        EVM stack.

    Returns
    -------
    value : `U256`
        The top element on the stack.

    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "stack" |)
            ],
            make_dict []
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some(M.get_name (| globals, "StackUnderflowError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, "stack" |), "pop" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition push : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "stack"; "value" ] |) in
    let _ := Constant.str "
    Pushes `value` onto `stack`.

    Parameters
    ----------
    stack :
        EVM stack.

    value :
        Item to be pushed onto `stack`.

    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "stack" |)
            ],
            make_dict []
          |),
          Constant.int 1024
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some(M.get_name (| globals, "StackOverflowError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, "stack" |), "append" |),
        make_list [
          M.get_name (| globals, "value" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).