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

Require ethereum.constantinople.fork_types.
Axiom ethereum_constantinople_fork_types_Address :
  IsGlobalAlias globals ethereum.constantinople.fork_types.globals "Address".

Require ethereum.constantinople.vm.precompiled_contracts.__init__.
Axiom ethereum_constantinople_vm_precompiled_contracts___init___ALT_BN128_ADD_ADDRESS :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.__init__.globals "ALT_BN128_ADD_ADDRESS".
Axiom ethereum_constantinople_vm_precompiled_contracts___init___ALT_BN128_MUL_ADDRESS :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.__init__.globals "ALT_BN128_MUL_ADDRESS".
Axiom ethereum_constantinople_vm_precompiled_contracts___init___ALT_BN128_PAIRING_CHECK_ADDRESS :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.__init__.globals "ALT_BN128_PAIRING_CHECK_ADDRESS".
Axiom ethereum_constantinople_vm_precompiled_contracts___init___ECRECOVER_ADDRESS :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.__init__.globals "ECRECOVER_ADDRESS".
Axiom ethereum_constantinople_vm_precompiled_contracts___init___IDENTITY_ADDRESS :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.__init__.globals "IDENTITY_ADDRESS".
Axiom ethereum_constantinople_vm_precompiled_contracts___init___MODEXP_ADDRESS :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.__init__.globals "MODEXP_ADDRESS".
Axiom ethereum_constantinople_vm_precompiled_contracts___init___RIPEMD160_ADDRESS :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.__init__.globals "RIPEMD160_ADDRESS".
Axiom ethereum_constantinople_vm_precompiled_contracts___init___SHA256_ADDRESS :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.__init__.globals "SHA256_ADDRESS".

Require ethereum.constantinople.vm.precompiled_contracts.alt_bn128.
Axiom ethereum_constantinople_vm_precompiled_contracts_alt_bn128_alt_bn128_add :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.alt_bn128.globals "alt_bn128_add".
Axiom ethereum_constantinople_vm_precompiled_contracts_alt_bn128_alt_bn128_mul :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.alt_bn128.globals "alt_bn128_mul".
Axiom ethereum_constantinople_vm_precompiled_contracts_alt_bn128_alt_bn128_pairing_check :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.alt_bn128.globals "alt_bn128_pairing_check".

Require ethereum.constantinople.vm.precompiled_contracts.ecrecover.
Axiom ethereum_constantinople_vm_precompiled_contracts_ecrecover_ecrecover :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.ecrecover.globals "ecrecover".

Require ethereum.constantinople.vm.precompiled_contracts.identity.
Axiom ethereum_constantinople_vm_precompiled_contracts_identity_identity :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.identity.globals "identity".

Require ethereum.constantinople.vm.precompiled_contracts.modexp.
Axiom ethereum_constantinople_vm_precompiled_contracts_modexp_modexp :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.modexp.globals "modexp".

Require ethereum.constantinople.vm.precompiled_contracts.ripemd160.
Axiom ethereum_constantinople_vm_precompiled_contracts_ripemd160_ripemd160 :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.ripemd160.globals "ripemd160".

Require ethereum.constantinople.vm.precompiled_contracts.sha256.
Axiom ethereum_constantinople_vm_precompiled_contracts_sha256_sha256 :
  IsGlobalAlias globals ethereum.constantinople.vm.precompiled_contracts.sha256.globals "sha256".

(* At top_level_stmt: unsupported node type: AnnAssign *)
