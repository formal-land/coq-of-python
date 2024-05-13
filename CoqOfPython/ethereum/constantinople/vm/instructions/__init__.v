Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.constantinople.vm.instructions.__init__".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_constantinople_vm_instructions_imports_arithmetic :
  IsImported globals "ethereum.constantinople.vm.instructions" "arithmetic".

Axiom ethereum_constantinople_vm_instructions_imports_bitwise :
  IsImported globals "ethereum.constantinople.vm.instructions" "bitwise".

Axiom ethereum_constantinople_vm_instructions_imports_block :
  IsImported globals "ethereum.constantinople.vm.instructions" "block".

Axiom ethereum_constantinople_vm_instructions_imports_comparison :
  IsImported globals "ethereum.constantinople.vm.instructions" "comparison".

Axiom ethereum_constantinople_vm_instructions_imports_control_flow :
  IsImported globals "ethereum.constantinople.vm.instructions" "control_flow".

Axiom ethereum_constantinople_vm_instructions_imports_environment :
  IsImported globals "ethereum.constantinople.vm.instructions" "environment".

Axiom ethereum_constantinople_vm_instructions_imports_keccak :
  IsImported globals "ethereum.constantinople.vm.instructions" "keccak".

Axiom ethereum_constantinople_vm_instructions_imports_log :
  IsImported globals "ethereum.constantinople.vm.instructions" "log".

Axiom ethereum_constantinople_vm_instructions_imports_memory :
  IsImported globals "ethereum.constantinople.vm.instructions" "memory".

Axiom ethereum_constantinople_vm_instructions_imports_stack :
  IsImported globals "ethereum.constantinople.vm.instructions" "stack".

Axiom ethereum_constantinople_vm_instructions_imports_storage :
  IsImported globals "ethereum.constantinople.vm.instructions" "storage".

Axiom ethereum_constantinople_vm_instructions_imports_system :
  IsImported globals "ethereum.constantinople.vm.instructions" "system".

Definition Ops : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
