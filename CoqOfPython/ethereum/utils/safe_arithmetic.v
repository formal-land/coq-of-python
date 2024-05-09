Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require typing.
Axiom typing_Optional :
  IsGlobalAlias globals typing.globals "Optional".
Axiom typing_Type_ :
  IsGlobalAlias globals typing.globals "Type_".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Definition u256_safe_add : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [  ] |) in
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
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [  ] |) in
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
    let result :=
      M.get_subscript (| M.get_name (| globals, "numbers" |), Constant.int 0 |) in
(* At stmt: unsupported node type: Try *)
    M.pure Constant.None_)).
