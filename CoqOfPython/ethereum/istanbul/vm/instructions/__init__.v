Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.istanbul.vm.instructions.__init__".

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

Axiom typing_imports :
  AreImported globals "typing" [ "Callable"; "Dict" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "arithmetic" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "bitwise" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "block" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "comparison" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "control_flow" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "environment" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "keccak" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "log" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "memory" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "stack" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "storage" ].

Axiom ethereum_istanbul_vm_instructions_imports :
  AreImported globals "ethereum.istanbul.vm.instructions" [ "system" ].

Definition Ops : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
