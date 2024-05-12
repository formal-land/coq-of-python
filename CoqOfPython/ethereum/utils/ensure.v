Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.utils.ensure".

Definition locals_stack : list Locals.t := [].

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

Axiom typing_imports_Type :
  IsImported globals "typing" "Type".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Definition ensure : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "value"; "exception" ] in
    ltac:(M.monadic (
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
      (* if *)
      M.if_then_else (|
        M.get_name (| globals, locals_stack, "value" |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.None_
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "exception" |)) |) in
    M.pure Constant.None_)).
