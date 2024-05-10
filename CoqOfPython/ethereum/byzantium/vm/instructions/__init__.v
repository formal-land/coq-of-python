Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.byzantium.vm.instructions.__init__".

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

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "arithmetic" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "bitwise" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "block" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "comparison" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "control_flow" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "environment" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "keccak" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "log" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "memory" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "stack" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "storage" ].

Axiom ethereum_byzantium_vm_instructions_imports :
  AreImported globals "ethereum.byzantium.vm.instructions" [ "system" ].

Definition Ops : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
