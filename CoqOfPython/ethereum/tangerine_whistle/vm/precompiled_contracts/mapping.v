Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Precompiled Contract Addresses
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Mapping of precompiled contracts their implementations.
".

Require typing.
Axiom typing_Callable :
  IsGlobalAlias globals typing.globals "Callable".
Axiom typing_Dict :
  IsGlobalAlias globals typing.globals "Dict".

Require ethereum.tangerine_whistle.fork_types.
Axiom ethereum_tangerine_whistle_fork_types_Address :
  IsGlobalAlias globals ethereum.tangerine_whistle.fork_types.globals "Address".

Require ethereum.tangerine_whistle.vm.precompiled_contracts.__init__.
Axiom ethereum_tangerine_whistle_vm_precompiled_contracts___init___ECRECOVER_ADDRESS :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.precompiled_contracts.__init__.globals "ECRECOVER_ADDRESS".
Axiom ethereum_tangerine_whistle_vm_precompiled_contracts___init___IDENTITY_ADDRESS :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.precompiled_contracts.__init__.globals "IDENTITY_ADDRESS".
Axiom ethereum_tangerine_whistle_vm_precompiled_contracts___init___RIPEMD160_ADDRESS :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.precompiled_contracts.__init__.globals "RIPEMD160_ADDRESS".
Axiom ethereum_tangerine_whistle_vm_precompiled_contracts___init___SHA256_ADDRESS :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.precompiled_contracts.__init__.globals "SHA256_ADDRESS".

Require ethereum.tangerine_whistle.vm.precompiled_contracts.ecrecover.
Axiom ethereum_tangerine_whistle_vm_precompiled_contracts_ecrecover_ecrecover :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.precompiled_contracts.ecrecover.globals "ecrecover".

Require ethereum.tangerine_whistle.vm.precompiled_contracts.identity.
Axiom ethereum_tangerine_whistle_vm_precompiled_contracts_identity_identity :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.precompiled_contracts.identity.globals "identity".

Require ethereum.tangerine_whistle.vm.precompiled_contracts.ripemd160.
Axiom ethereum_tangerine_whistle_vm_precompiled_contracts_ripemd160_ripemd160 :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.precompiled_contracts.ripemd160.globals "ripemd160".

Require ethereum.tangerine_whistle.vm.precompiled_contracts.sha256.
Axiom ethereum_tangerine_whistle_vm_precompiled_contracts_sha256_sha256 :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.precompiled_contracts.sha256.globals "sha256".

(* At top_level_stmt: unsupported node type: AnnAssign *)
