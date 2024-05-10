Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.paris.vm.instructions.__init__".

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

Axiom typing_imports_Callable :
  IsImported globals "typing" "Callable".
Axiom typing_imports_Dict :
  IsImported globals "typing" "Dict".

Axiom ethereum_paris_vm_instructions_imports_arithmetic :
  IsImported globals "ethereum.paris.vm.instructions" "arithmetic".

Axiom ethereum_paris_vm_instructions_imports_bitwise :
  IsImported globals "ethereum.paris.vm.instructions" "bitwise".

Axiom ethereum_paris_vm_instructions_imports_block :
  IsImported globals "ethereum.paris.vm.instructions" "block".

Axiom ethereum_paris_vm_instructions_imports_comparison :
  IsImported globals "ethereum.paris.vm.instructions" "comparison".

Axiom ethereum_paris_vm_instructions_imports_control_flow :
  IsImported globals "ethereum.paris.vm.instructions" "control_flow".

Axiom ethereum_paris_vm_instructions_imports_environment :
  IsImported globals "ethereum.paris.vm.instructions" "environment".

Axiom ethereum_paris_vm_instructions_imports_keccak :
  IsImported globals "ethereum.paris.vm.instructions" "keccak".

Axiom ethereum_paris_vm_instructions_imports_log :
  IsImported globals "ethereum.paris.vm.instructions" "log".

Axiom ethereum_paris_vm_instructions_imports_memory :
  IsImported globals "ethereum.paris.vm.instructions" "memory".

Axiom ethereum_paris_vm_instructions_imports_stack :
  IsImported globals "ethereum.paris.vm.instructions" "stack".

Axiom ethereum_paris_vm_instructions_imports_storage :
  IsImported globals "ethereum.paris.vm.instructions" "storage".

Axiom ethereum_paris_vm_instructions_imports_system :
  IsImported globals "ethereum.paris.vm.instructions" "system".

Definition Ops : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
