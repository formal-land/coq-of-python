Require Import CoqOfPython.CoqOfPython.
Require Import proofs.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import proofs.heap.

Require ethereum.paris.vm.instructions.simulations.arithmetic.
Require ethereum.paris.vm.instructions.arithmetic.
Require ethereum.paris.vm.stack.

Require ethereum.simulations.base_types.
Module U256 := base_types.U256.

Import Run.

Module Option.
  Definition map {A B} (f : A -> B) (x : option A) : option B :=
    match x with
    | Some x => Some (f x)
    | None => None
    end.
End Option.

Module AddLocals.
  Record t : Set := {
    x : option U256.t;
    y : option U256.t;
    result : option U256.t;
  }.

  Definition init : t :=
    {|
      x := None;
      y := None;
      result := None;
    |}.

  Definition to_object (locals : t) : Object.t Value.t :=
    Object.make [
      ("x", Option.map U256.to_value locals.(x));
      ("y", Option.map U256.to_value locals.(y));
      ("result", Option.map U256.to_value locals.(result))
    ].
End AddLocals.

Lemma run_add (stack : Stack.t) (heap : Heap.t) :
  let '(result, evm') := simulations.arithmetic.add heap.(Heap.evm) in
  let result :=
    match result with
    | inl tt => inl Constant.None_
    | inr exn => inr (Exception.Raise (Some Constant.None_))
    end in
  let heap' := heap <| Heap.evm := evm' |> in
  exists fresh_stack,
  {{ stack, heap |
    arithmetic.add (make_list []) (make_dict []) ⇓
    result
  | stack ++ fresh_stack, heap' }}.
Proof.
  destruct simulations.arithmetic.add as [result evm'] eqn:?.
  unfold arithmetic.add, simulations.arithmetic.add in *.
  cbn in *.
  eexists.
  apply (Run.CallPrimitiveStateAllocStack AddLocals.init AddLocals.to_object); [reflexivity |].
  cbn.
  eapply Run.CallPrimitiveStateReadStack.
  { now erewrite Stack.read_length_eq. }
  { cbn.
    eapply Run.CallPrimitiveGetInGlobals.
    { apply arithmetic.ethereum_paris_vm_stack_imports_pop.
      apply stack.pop_in_globals.
    }
    { admit. }
  }
Admitted.
