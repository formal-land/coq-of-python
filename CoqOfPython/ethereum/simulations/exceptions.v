Require Import CoqOfPython.CoqOfPython.
Require ethereum.paris.vm.simulations.exceptions.

Module EthereumException.
  Inductive t : Set :=
  | ExceptionalHalt (exn : exceptions.ExceptionalHalt.t).
End EthereumException.
