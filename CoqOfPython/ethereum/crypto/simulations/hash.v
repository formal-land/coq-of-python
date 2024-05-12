Require Import CoqOfPython.CoqOfPython.

Require ethereum.simulations.base_types.
Module Bytes := base_types.Bytes.
Module Bytes32 := base_types.Bytes32.
Module Bytes64 := base_types.Bytes64.

Module Hash32.
  Inductive t : Set :=
  | Make (hash : Bytes32.t).

  Definition get (hash : t) : Bytes32.t :=
    match hash with
    | Make hash => hash
    end.
End Hash32.

Module Hash64.
  Inductive t : Set :=
  | Make (hash : Bytes64.t).

  Definition get (hash : t) : Bytes64.t :=
    match hash with
    | Make hash => hash
    end.
End Hash64.
