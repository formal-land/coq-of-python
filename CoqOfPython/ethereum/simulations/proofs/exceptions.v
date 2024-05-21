Require Import CoqOfPython.CoqOfPython.
Require Import simulations.proofs.CoqOfPython.
Require Import simulations.proofs.heap.

Require ethereum.paris.vm.simulations.proofs.exceptions.
Require ethereum.simulations.exceptions.

Import Run.

Module EthereumException.
  Definition to_value (exn : exceptions.EthereumException.t) : Value.t :=
    match exn with
    | exceptions.EthereumException.ExceptionalHalt exn =>
      Value.Make "exceptions" "ExceptionalHalt" (Pointer.Imm Object.empty)
    end.
End EthereumException.
