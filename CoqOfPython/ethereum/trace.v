Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.trace".

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

Axiom dataclasses_imports :
  AreImported globals "dataclasses" [ "dataclass" ].

Axiom typing_imports :
  AreImported globals "typing" [ "Optional"; "Union" ].

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
    M.get_name (| globals, "Union" |),
    make_tuple [ M.get_name (| globals, "TransactionStart" |); M.get_name (| globals, "TransactionEnd" |); M.get_name (| globals, "PrecompileStart" |); M.get_name (| globals, "PrecompileEnd" |); M.get_name (| globals, "OpStart" |); M.get_name (| globals, "OpEnd" |); M.get_name (| globals, "OpException" |); M.get_name (| globals, "EvmStop" |); M.get_name (| globals, "GasAndRefund" |) ]
  |)
)).

Definition evm_trace : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "event"; "trace_memory"; "trace_stack"; "trace_return_data" ] |) in
    let _ := Constant.str "
    Create a trace of the event.
    " in
    let _ := M.pass (| |) in
    M.pure Constant.None_)).
