Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
EVM Instruction Encoding (Opcodes)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Machine readable representations of EVM instructions, and a mapping to their
implementations.
".

(* At top_level_stmt: unsupported node type: Import *)

Require typing.
Axiom typing_Callable :
  IsGlobalAlias globals typing.globals "Callable".
Axiom typing_Dict :
  IsGlobalAlias globals typing.globals "Dict".

Require __init__.
Axiom __init___arithmetic :
  IsGlobalAlias globals __init__.globals "arithmetic".

Require __init__.
Axiom __init___bitwise :
  IsGlobalAlias globals __init__.globals "bitwise".

Require __init__.
Axiom __init___block :
  IsGlobalAlias globals __init__.globals "block".

Require __init__.
Axiom __init___comparison :
  IsGlobalAlias globals __init__.globals "comparison".

Require __init__.
Axiom __init___control_flow :
  IsGlobalAlias globals __init__.globals "control_flow".

Require __init__.
Axiom __init___environment :
  IsGlobalAlias globals __init__.globals "environment".

Require __init__.
Axiom __init___keccak :
  IsGlobalAlias globals __init__.globals "keccak".

Require __init__.
Axiom __init___log :
  IsGlobalAlias globals __init__.globals "log".

Require __init__.
Axiom __init___memory :
  IsGlobalAlias globals __init__.globals "memory".

Require __init__.
Axiom __init___stack :
  IsGlobalAlias globals __init__.globals "stack".

Require __init__.
Axiom __init___storage :
  IsGlobalAlias globals __init__.globals "storage".

Require __init__.
Axiom __init___system :
  IsGlobalAlias globals __init__.globals "system".

Definition Ops : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
