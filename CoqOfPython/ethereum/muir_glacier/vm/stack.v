Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.muir_glacier.vm.stack".

Definition locals_stack : list Locals.t := [].

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

Axiom typing_imports_List :
  IsImported globals "typing" "List".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".

Axiom ethereum_muir_glacier_vm_exceptions_imports_StackOverflowError :
  IsImported globals "ethereum.muir_glacier.vm.exceptions" "StackOverflowError".
Axiom ethereum_muir_glacier_vm_exceptions_imports_StackUnderflowError :
  IsImported globals "ethereum.muir_glacier.vm.exceptions" "StackUnderflowError".

Definition pop : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "stack" ] in
    ltac:(M.monadic (
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
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "stack" |)
            ],
            make_dict []
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "StackUnderflowError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "stack" |), "pop" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom pop_in_globals :
  IsInGlobals globals "pop" (make_function pop).

Definition push : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "stack"; "value" ] in
    ltac:(M.monadic (
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
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "stack" |)
            ],
            make_dict []
          |),
          Constant.int 1024
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "StackOverflowError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "stack" |), "append" |),
        make_list [
          M.get_name (| globals, locals_stack, "value" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom push_in_globals :
  IsInGlobals globals "push" (make_function push).
