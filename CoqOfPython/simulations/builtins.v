Require Import CoqOfPython.CoqOfPython.
Require ethereum.simulations.exceptions.

Module ArithmeticError.
  Inductive t : Set :=
  | OverflowError.
End ArithmeticError.

Module Exception.
  (** Here we exhaustively desbribe which are the possible exceptions. *)
  Inductive t : Set :=
  | ArithmeticError (exn : ArithmeticError.t)
  | EthereumException (exn : exceptions.EthereumException.t).
End Exception.
