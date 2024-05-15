(** * The memory that we use to interpret the translated Python code. *)
Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.proofs.CoqOfPython.

Require ethereum.simulations.base_types.
Module Uint := base_types.Uint.
Module U256 := base_types.U256.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.

Module Address.
  Inductive t : Set :=
  | evm
  | stack.
End Address.

Module Heap.
  Module Evm.
    Record t : Set := {
      pc : Uint.t;
      gas_left : Uint.t;
    }.
  End Evm.

  Record t : Set := {
    evm : Evm.t;
    stack : list U256.t;
  }.

  Global Instance I : Heap.Trait Heap.t Address.t := {
    get_Set a :=
      match a with
      | Address.evm => Evm.t
      | Address.stack => list U256.t
      end;
    read a h :=
      match a with
      | Address.evm => Some h.(evm)
      | Address.stack => Some h.(stack)
      end;
    alloc_write a h :=
      match a with
      | Address.evm => fun v => Some (h <| evm := v |>)
      | Address.stack => fun v => Some (h <| stack := v |>)
      end;
  }.

  Lemma is_valid : Heap.Valid.t I.
  Proof.
    sauto.
  Qed.

  Definition to_message (heap : t) : __init__.Message.t __init__.Evm.t.
  Admitted. (* TODO *)

  (*Definition of_evm (evm : ethereum.paris.vm.simulations.__init__.Evm.t) : t :=
    {|
      evm := {|
        Evm.pc := Evm.Lens.pc.(Lens.read) evm;
        Evm.gas_left := Evm.Lens.gas_left.(Lens.read) evm;
      |};
      stack := Evm.Lens.stack.(Lens.read) evm;
    |}.*)

  Definition to_evm (heap : t) : __init__.Evm.t :=
    __init__.Evm.Make (to_message heap) {|
      __init__.Evm.Rest.pc := heap.(evm).(Evm.pc);
      __init__.Evm.Rest.stack := heap.(stack);
      __init__.Evm.Rest.gas_left := heap.(evm).(Evm.gas_left);
    |}.
End Heap.
