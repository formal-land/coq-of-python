Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.utils.safe_arithmetic".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Safe Arithmetic for U256 Integer Type
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Safe arithmetic utility functions for U256 integer type.
".

Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Type :
  IsImported globals "typing" "Type".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Definition u256_safe_add : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [  ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Adds together the given sequence of numbers. If the total sum of the
    numbers exceeds `U256.MAX_VALUE` then an exception is raised.
    If `exception_type` = None then the exception raised defaults to the one
    raised by `U256` when `U256.value > U256.MAX_VALUE`
    else `exception_type` is raised.

    Parameters
    ----------
    numbers :
        The sequence of numbers that need to be added together.

    exception_type:
        The exception that needs to be raised if the sum of the `numbers`
        exceeds `U256.MAX_VALUE`.

    Returns
    -------
    result : `ethereum.base_types.U256`
        The sum of the given sequence of numbers if the total is less than
        `U256.MAX_VALUE` else an exception is raised.
        If `exception_type` = None then the exception raised defaults to the
        one raised by `U256` when `U256.value > U256.MAX_VALUE`
        else `exception_type` is raised.
    " in
(* At stmt: unsupported node type: Try *)
    M.pure Constant.None_)).

Definition u256_safe_multiply : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [  ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Multiplies together the given sequence of numbers. If the net product of
    the numbers exceeds `U256.MAX_VALUE` then an exception is raised.
    If `exception_type` = None then the exception raised defaults to the one
    raised by `U256` when `U256.value > U256.MAX_VALUE` else
    `exception_type` is raised.

    Parameters
    ----------
    numbers :
        The sequence of numbers that need to be multiplies together.

    exception_type:
        The exception that needs to be raised if the sum of the `numbers`
        exceeds `U256.MAX_VALUE`.

    Returns
    -------
    result : `ethereum.base_types.U256`
        The multiplication product of the given sequence of numbers if the
        net product  is less than `U256.MAX_VALUE` else an exception is raised.
        If `exception_type` = None then the exception raised defaults to the
        one raised by `U256` when `U256.value > U256.MAX_VALUE`
        else `exception_type` is raised.
    " in
    let _ := M.assign_local (|
      "result" ,
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "numbers" |),
        Constant.int 0
      |)
    |) in
(* At stmt: unsupported node type: Try *)
    M.pure Constant.None_)).
