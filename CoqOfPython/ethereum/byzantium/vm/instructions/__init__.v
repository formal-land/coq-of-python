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

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___arithmetic :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "arithmetic".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___bitwise :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "bitwise".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___block :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "block".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___comparison :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "comparison".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___control_flow :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "control_flow".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___environment :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "environment".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___keccak :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "keccak".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___log :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "log".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___memory :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "memory".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___stack :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "stack".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___storage :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "storage".

Require ethereum.byzantium.vm.instructions.__init__.
Axiom ethereum_byzantium_vm_instructions___init___system :
  IsGlobalAlias globals ethereum.byzantium.vm.instructions.__init__.globals "system".

Definition Ops : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: AnnAssign *)