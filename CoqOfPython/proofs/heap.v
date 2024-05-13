(** * The memory that we use to interpret the translated Python code. *)
Require Import CoqOfPython.CoqOfPython.
Require Import proofs.CoqOfPython.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.

Module Address.
  Inductive t : Set :=
  | Evm.
End Address.

Module Heap.
  Record t : Set := {
    evm : Evm.t;
  }.

  Global Instance I : Heap.Trait Heap.t Address.t := {
    get_Set a :=
      match a with
      | Address.Evm => Evm.t
      end;
    read a h :=
      match a with
      | Address.Evm => Some h.(evm)
      end;
    alloc_write a h :=
      match a with
      | Address.Evm => fun v => Some (h <| evm := v |>)
      end;
  }.

  Lemma is_valid : Heap.Valid.t I.
  Proof.
    sauto.
  Qed.
End Heap.
