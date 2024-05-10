Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.dao_fork.vm.precompiled_contracts.mapping".

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

Axiom ethereum_dao_fork_fork_types_imports :
  AreImported globals "ethereum.dao_fork.fork_types" [ "Address" ].

Axiom ethereum_dao_fork_vm_precompiled_contracts_imports :
  AreImported globals "ethereum.dao_fork.vm.precompiled_contracts" [ "ECRECOVER_ADDRESS"; "IDENTITY_ADDRESS"; "RIPEMD160_ADDRESS"; "SHA256_ADDRESS" ].

Axiom ethereum_dao_fork_vm_precompiled_contracts_ecrecover_imports :
  AreImported globals "ethereum.dao_fork.vm.precompiled_contracts.ecrecover" [ "ecrecover" ].

Axiom ethereum_dao_fork_vm_precompiled_contracts_identity_imports :
  AreImported globals "ethereum.dao_fork.vm.precompiled_contracts.identity" [ "identity" ].

Axiom ethereum_dao_fork_vm_precompiled_contracts_ripemd160_imports :
  AreImported globals "ethereum.dao_fork.vm.precompiled_contracts.ripemd160" [ "ripemd160" ].

Axiom ethereum_dao_fork_vm_precompiled_contracts_sha256_imports :
  AreImported globals "ethereum.dao_fork.vm.precompiled_contracts.sha256" [ "sha256" ].

(* At top_level_stmt: unsupported node type: AnnAssign *)
