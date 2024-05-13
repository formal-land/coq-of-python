Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.trace".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
.. _trace:

EVM Trace
^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Defines the functions required for creating evm traces during execution.
".

(* At top_level_stmt: unsupported node type: Import *)

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Definition TransactionStart : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition TransactionEnd : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition PrecompileStart : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition PrecompileEnd : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition OpStart : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition OpEnd : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition OpException : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition EvmStop : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition GasAndRefund : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition TraceEvent : Value.t := M.run ltac:(M.monadic (
  M.get_subscript (|
    M.get_name (| globals, locals_stack, "Union" |),
    make_tuple [ M.get_name (| globals, locals_stack, "TransactionStart" |); M.get_name (| globals, locals_stack, "TransactionEnd" |); M.get_name (| globals, locals_stack, "PrecompileStart" |); M.get_name (| globals, locals_stack, "PrecompileEnd" |); M.get_name (| globals, locals_stack, "OpStart" |); M.get_name (| globals, locals_stack, "OpEnd" |); M.get_name (| globals, locals_stack, "OpException" |); M.get_name (| globals, locals_stack, "EvmStop" |); M.get_name (| globals, locals_stack, "GasAndRefund" |) ]
  |)
)).

Definition evm_trace : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm"; "event"; "trace_memory"; "trace_stack"; "trace_return_data" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Create a trace of the event.
    " in
    let _ := M.pass (| |) in
    M.pure Constant.None_)).

Axiom evm_trace_in_globals :
  IsInGlobals globals "evm_trace" (make_function evm_trace).
