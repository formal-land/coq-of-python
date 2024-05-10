Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.berlin.vm.instructions.__init__".

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

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "arithmetic" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "bitwise" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "block" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "comparison" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "control_flow" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "environment" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "keccak" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "log" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "memory" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "stack" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "storage" ].

Axiom ethereum_berlin_vm_instructions_imports :
  AreImported globals "ethereum.berlin.vm.instructions" [ "system" ].

Definition Ops : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
