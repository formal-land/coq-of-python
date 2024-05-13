Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require Import simulations.base_types.
Module U256 := base_types.U256.

Import simulations.CoqOfPython.Notations.

Definition pop : MS? (list U256.t) Exception.t U256.t :=
  fun stack =>
    match stack with
    | [] =>
      (
        inr (Exception.EthereumException (
          exceptions.EthereumException.ExceptionalHalt
            exceptions.ExceptionalHalt.StackUnderflowError
        )),
        stack
      )
    | x :: rest => (inl x, rest)
    end.

Definition push (value : U256.t) : MS? (list U256.t) Exception.t unit :=
  fun stack =>
    if Z.of_nat (List.length stack) =? 1024 then
      (
        inr (Exception.EthereumException (
          exceptions.EthereumException.ExceptionalHalt
            exceptions.ExceptionalHalt.StackOverflowError
        )),
        stack
      )
    else
      (inl tt, value :: stack).
