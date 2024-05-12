Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Module U256 := base_types.U256.
Module Uint := base_types.Uint.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.

Import simulations.CoqOfPython.Notations.

Definition GAS_JUMPDEST := Uint.Make 1.
Definition GAS_BASE := Uint.Make 2.
Definition GAS_VERY_LOW := Uint.Make 3.
Definition GAS_STORAGE_SET := Uint.Make 20000.
Definition GAS_STORAGE_UPDATE := Uint.Make 5000.
Definition GAS_STORAGE_CLEAR_REFUND := Uint.Make 4800.
Definition GAS_LOW := Uint.Make 5.
Definition GAS_MID := Uint.Make 8.
Definition GAS_HIGH := Uint.Make 10.
Definition GAS_EXPONENTIATION := Uint.Make 10.
Definition GAS_EXPONENTIATION_PER_BYTE := Uint.Make 50.
Definition GAS_MEMORY := Uint.Make 3.
Definition GAS_KECCAK256 := Uint.Make 30.
Definition GAS_KECCAK256_WORD := Uint.Make 6.
Definition GAS_COPY := Uint.Make 3.
Definition GAS_BLOCK_HASH := Uint.Make 20.
Definition GAS_LOG := Uint.Make 375.
Definition GAS_LOG_DATA := Uint.Make 8.
Definition GAS_LOG_TOPIC := Uint.Make 375.
Definition GAS_CREATE := Uint.Make 32000.
Definition GAS_CODE_DEPOSIT := Uint.Make 200.
Definition GAS_ZERO := Uint.Make 0.
Definition GAS_NEW_ACCOUNT := Uint.Make 25000.
Definition GAS_CALL_VALUE := Uint.Make 9000.
Definition GAS_CALL_STIPEND := Uint.Make 2300.
Definition GAS_SELF_DESTRUCT := Uint.Make 5000.
Definition GAS_SELF_DESTRUCT_NEW_ACCOUNT := Uint.Make 25000.
Definition GAS_ECRECOVER := Uint.Make 3000.
Definition GAS_SHA256 := Uint.Make 60.
Definition GAS_SHA256_WORD := Uint.Make 12.
Definition GAS_RIPEMD160 := Uint.Make 600.
Definition GAS_RIPEMD160_WORD := Uint.Make 120.
Definition GAS_IDENTITY := Uint.Make 15.
Definition GAS_IDENTITY_WORD := Uint.Make 3.
Definition GAS_RETURN_DATA_COPY := Uint.Make 3.
Definition GAS_FAST_STEP := Uint.Make 5.
Definition GAS_BLAKE2_PER_ROUND := Uint.Make 1.
Definition GAS_COLD_SLOAD := Uint.Make 2100.
Definition GAS_COLD_ACCOUNT_ACCESS := Uint.Make 2600.
Definition GAS_WARM_ACCESS := Uint.Make 100.

Parameter charge_gas : forall (amount : Uint.t), MS? Evm.t Exception.t unit.
