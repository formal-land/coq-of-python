Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.muir_glacier.vm.precompiled_contracts.mapping".

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

Axiom typing_imports :
  AreImported globals "typing" [ "Callable"; "Dict" ].

Axiom ethereum_muir_glacier_fork_types_imports :
  AreImported globals "ethereum.muir_glacier.fork_types" [ "Address" ].

Axiom ethereum_muir_glacier_vm_precompiled_contracts_imports :
  AreImported globals "ethereum.muir_glacier.vm.precompiled_contracts" [ "ALT_BN128_ADD_ADDRESS"; "ALT_BN128_MUL_ADDRESS"; "ALT_BN128_PAIRING_CHECK_ADDRESS"; "BLAKE2F_ADDRESS"; "ECRECOVER_ADDRESS"; "IDENTITY_ADDRESS"; "MODEXP_ADDRESS"; "RIPEMD160_ADDRESS"; "SHA256_ADDRESS" ].

Axiom ethereum_muir_glacier_vm_precompiled_contracts_alt_bn128_imports :
  AreImported globals "ethereum.muir_glacier.vm.precompiled_contracts.alt_bn128" [ "alt_bn128_add"; "alt_bn128_mul"; "alt_bn128_pairing_check" ].

Axiom ethereum_muir_glacier_vm_precompiled_contracts_blake2f_imports :
  AreImported globals "ethereum.muir_glacier.vm.precompiled_contracts.blake2f" [ "blake2f" ].

Axiom ethereum_muir_glacier_vm_precompiled_contracts_ecrecover_imports :
  AreImported globals "ethereum.muir_glacier.vm.precompiled_contracts.ecrecover" [ "ecrecover" ].

Axiom ethereum_muir_glacier_vm_precompiled_contracts_identity_imports :
  AreImported globals "ethereum.muir_glacier.vm.precompiled_contracts.identity" [ "identity" ].

Axiom ethereum_muir_glacier_vm_precompiled_contracts_modexp_imports :
  AreImported globals "ethereum.muir_glacier.vm.precompiled_contracts.modexp" [ "modexp" ].

Axiom ethereum_muir_glacier_vm_precompiled_contracts_ripemd160_imports :
  AreImported globals "ethereum.muir_glacier.vm.precompiled_contracts.ripemd160" [ "ripemd160" ].

Axiom ethereum_muir_glacier_vm_precompiled_contracts_sha256_imports :
  AreImported globals "ethereum.muir_glacier.vm.precompiled_contracts.sha256" [ "sha256" ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
