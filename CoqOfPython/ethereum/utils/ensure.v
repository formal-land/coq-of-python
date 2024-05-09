Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ensure (Assertion) Utilities
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Functions that simplify checking assertions and raising exceptions.
".

Require typing.
Axiom typing_Type_ :
  IsGlobalAlias globals typing.globals "Type_".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Definition ensure : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "value"; "exception" ] |) in
    let _ := Constant.str "
    Does nothing if `value` is truthy, otherwise raises the exception returned
    by `exception_class`.

    Parameters
    ----------

    value :
        Value that should be true.

    exception :
        Constructor for the exception to raise.
    " in
    let _ :=
        M.pure Constant.None_
      )) |) in
    let _ := M.raise (| Some(M.get_name (| globals, "exception" |))
    M.pure Constant.None_)).
