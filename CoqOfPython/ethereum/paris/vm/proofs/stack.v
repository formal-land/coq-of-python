Require Import CoqOfPython.CoqOfPython.
Require Import proofs.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import proofs.heap.

Require ethereum.paris.vm.simulations.stack.
Require ethereum.paris.vm.stack.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.

Import Run.

Lemma run_pop (stack : Stack.t) (heap : Heap.t) :
  let '(result, evm') :=
    StateError.lift_lens Evm.Lens.stack simulations.stack.pop heap.(Heap.evm) in
  let result :=
    match result with
    | inl s' => inl Constant.None_
    | inr exn => inr (Exception.Raise (Some Constant.None_))
    end in
  let heap' := heap <| Heap.evm := evm' |> in
  exists fresh_stack,
  {{ stack, heap |
    stack.pop (make_list []) (make_dict []) ⇓
    result
  | stack ++ fresh_stack, heap' }}.
Proof.
  destruct StateError.lift_lens as [result evm'] eqn:?.
  unfold stack.pop, simulations.stack.pop in *.
  cbn in *.
  eexists.
Admitted.
