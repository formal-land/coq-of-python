Require Import CoqOfPython.CoqOfPython.
Require ethereum.simulations.base_types.


Module Address.
  Inductive t : Set :=
  | Make (address : base_types.Bytes20.t).

  Definition get (address : t) : base_types.Bytes20.t :=
    match address with
    | Make address => address
    end.
End Address.
