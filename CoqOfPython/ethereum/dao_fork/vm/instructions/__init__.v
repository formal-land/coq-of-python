Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.dao_fork.vm.instructions.__init__".

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

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "arithmetic" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "bitwise" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "block" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "comparison" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "control_flow" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "environment" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "keccak" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "log" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "memory" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "stack" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "storage" ].

Axiom ethereum_dao_fork_vm_instructions_imports :
  AreImported globals "ethereum.dao_fork.vm.instructions" [ "system" ].

Definition Ops : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
