Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Definition U255_CEIL_VALUE := base_types.U255_CEIL_VALUE.
Module U256 := base_types.U256.
Definition U256_CEIL_VALUE := base_types.U256_CEIL_VALUE.
Module Uint := base_types.Uint.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.

Require ethereum.paris.vm.simulations.gas.
Definition GAS_EXPONENTIATION := gas.GAS_EXPONENTIATION.
Definition GAS_EXPONENTIATION_PER_BYTE := gas.GAS_EXPONENTIATION_PER_BYTE.
Definition GAS_LOW := gas.GAS_LOW.
Definition GAS_MID := gas.GAS_MID.
Definition GAS_VERY_LOW := gas.GAS_VERY_LOW.
Definition charge_gas := gas.charge_gas.

Require ethereum.paris.vm.simulations.stack.
Definition pop := stack.pop.
Definition push := stack.push.

Import simulations.CoqOfPython.Notations.

Definition add : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  letS? y := StateError.lift_lens Evm.Lens.stack pop in

  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in

  (* OPERATION *)
  let result := U256.wrapping_add x y in

  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc => (inl tt, Uint.__add__ pc (Uint.Make 1))) in

  returnS? tt.
