Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.cancun.vm.instructions.__init__".

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

Axiom ethereum_cancun_vm_instructions_imports_arithmetic :
  IsImported globals "ethereum.cancun.vm.instructions" "arithmetic".

Axiom ethereum_cancun_vm_instructions_imports_bitwise :
  IsImported globals "ethereum.cancun.vm.instructions" "bitwise".

Axiom ethereum_cancun_vm_instructions_imports_block :
  IsImported globals "ethereum.cancun.vm.instructions" "block".

Axiom ethereum_cancun_vm_instructions_imports_comparison :
  IsImported globals "ethereum.cancun.vm.instructions" "comparison".

Axiom ethereum_cancun_vm_instructions_imports_control_flow :
  IsImported globals "ethereum.cancun.vm.instructions" "control_flow".

Axiom ethereum_cancun_vm_instructions_imports_environment :
  IsImported globals "ethereum.cancun.vm.instructions" "environment".

Axiom ethereum_cancun_vm_instructions_imports_keccak :
  IsImported globals "ethereum.cancun.vm.instructions" "keccak".

Axiom ethereum_cancun_vm_instructions_imports_log :
  IsImported globals "ethereum.cancun.vm.instructions" "log".

Axiom ethereum_cancun_vm_instructions_imports_memory :
  IsImported globals "ethereum.cancun.vm.instructions" "memory".

Axiom ethereum_cancun_vm_instructions_imports_stack :
  IsImported globals "ethereum.cancun.vm.instructions" "stack".

Axiom ethereum_cancun_vm_instructions_imports_storage :
  IsImported globals "ethereum.cancun.vm.instructions" "storage".

Axiom ethereum_cancun_vm_instructions_imports_system :
  IsImported globals "ethereum.cancun.vm.instructions" "system".

Definition Ops : Value.t := builtins.make_klass {|
  Klass.bases := [
    (* At base: unsupported node type: Attribute *)
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

(* At top_level_stmt: unsupported node type: AnnAssign *)
