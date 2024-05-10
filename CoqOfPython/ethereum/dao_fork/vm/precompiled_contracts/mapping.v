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

Axiom typing_imports_Callable :
  IsImported globals "typing" "Callable".
Axiom typing_imports_Dict :
  IsImported globals "typing" "Dict".

Axiom ethereum_dao_fork_fork_types_imports_Address :
  IsImported globals "ethereum.dao_fork.fork_types" "Address".

Axiom ethereum_dao_fork_vm_precompiled_contracts_imports_ECRECOVER_ADDRESS :
  IsImported globals "ethereum.dao_fork.vm.precompiled_contracts" "ECRECOVER_ADDRESS".
Axiom ethereum_dao_fork_vm_precompiled_contracts_imports_IDENTITY_ADDRESS :
  IsImported globals "ethereum.dao_fork.vm.precompiled_contracts" "IDENTITY_ADDRESS".
Axiom ethereum_dao_fork_vm_precompiled_contracts_imports_RIPEMD160_ADDRESS :
  IsImported globals "ethereum.dao_fork.vm.precompiled_contracts" "RIPEMD160_ADDRESS".
Axiom ethereum_dao_fork_vm_precompiled_contracts_imports_SHA256_ADDRESS :
  IsImported globals "ethereum.dao_fork.vm.precompiled_contracts" "SHA256_ADDRESS".

Axiom ethereum_dao_fork_vm_precompiled_contracts_ecrecover_imports_ecrecover :
  IsImported globals "ethereum.dao_fork.vm.precompiled_contracts.ecrecover" "ecrecover".

Axiom ethereum_dao_fork_vm_precompiled_contracts_identity_imports_identity :
  IsImported globals "ethereum.dao_fork.vm.precompiled_contracts.identity" "identity".

Axiom ethereum_dao_fork_vm_precompiled_contracts_ripemd160_imports_ripemd160 :
  IsImported globals "ethereum.dao_fork.vm.precompiled_contracts.ripemd160" "ripemd160".

Axiom ethereum_dao_fork_vm_precompiled_contracts_sha256_imports_sha256 :
  IsImported globals "ethereum.dao_fork.vm.precompiled_contracts.sha256" "sha256".

(* At top_level_stmt: unsupported node type: AnnAssign *)
