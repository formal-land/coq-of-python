Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.shanghai.vm.precompiled_contracts.mapping".

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

Axiom typing_imports_Callable :
  IsImported globals "typing" "Callable".
Axiom typing_imports_Dict :
  IsImported globals "typing" "Dict".

Axiom ethereum_shanghai_fork_types_imports_Address :
  IsImported globals "ethereum.shanghai.fork_types" "Address".

Axiom ethereum_shanghai_vm_precompiled_contracts_imports_ALT_BN128_ADD_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "ALT_BN128_ADD_ADDRESS".
Axiom ethereum_shanghai_vm_precompiled_contracts_imports_ALT_BN128_MUL_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "ALT_BN128_MUL_ADDRESS".
Axiom ethereum_shanghai_vm_precompiled_contracts_imports_ALT_BN128_PAIRING_CHECK_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "ALT_BN128_PAIRING_CHECK_ADDRESS".
Axiom ethereum_shanghai_vm_precompiled_contracts_imports_BLAKE2F_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "BLAKE2F_ADDRESS".
Axiom ethereum_shanghai_vm_precompiled_contracts_imports_ECRECOVER_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "ECRECOVER_ADDRESS".
Axiom ethereum_shanghai_vm_precompiled_contracts_imports_IDENTITY_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "IDENTITY_ADDRESS".
Axiom ethereum_shanghai_vm_precompiled_contracts_imports_MODEXP_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "MODEXP_ADDRESS".
Axiom ethereum_shanghai_vm_precompiled_contracts_imports_RIPEMD160_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "RIPEMD160_ADDRESS".
Axiom ethereum_shanghai_vm_precompiled_contracts_imports_SHA256_ADDRESS :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts" "SHA256_ADDRESS".

Axiom ethereum_shanghai_vm_precompiled_contracts_alt_bn128_imports_alt_bn128_add :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.alt_bn128" "alt_bn128_add".
Axiom ethereum_shanghai_vm_precompiled_contracts_alt_bn128_imports_alt_bn128_mul :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.alt_bn128" "alt_bn128_mul".
Axiom ethereum_shanghai_vm_precompiled_contracts_alt_bn128_imports_alt_bn128_pairing_check :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.alt_bn128" "alt_bn128_pairing_check".

Axiom ethereum_shanghai_vm_precompiled_contracts_blake2f_imports_blake2f :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.blake2f" "blake2f".

Axiom ethereum_shanghai_vm_precompiled_contracts_ecrecover_imports_ecrecover :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.ecrecover" "ecrecover".

Axiom ethereum_shanghai_vm_precompiled_contracts_identity_imports_identity :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.identity" "identity".

Axiom ethereum_shanghai_vm_precompiled_contracts_modexp_imports_modexp :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.modexp" "modexp".

Axiom ethereum_shanghai_vm_precompiled_contracts_ripemd160_imports_ripemd160 :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.ripemd160" "ripemd160".

Axiom ethereum_shanghai_vm_precompiled_contracts_sha256_imports_sha256 :
  IsImported globals "ethereum.shanghai.vm.precompiled_contracts.sha256" "sha256".

(* At top_level_stmt: unsupported node type: AnnAssign *)
