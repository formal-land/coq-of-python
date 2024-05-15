Require Import CoqOfPython.CoqOfPython.
Require Import proofs.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import proofs.heap.

Require ethereum.paris.vm.simulations.stack.
Require ethereum.paris.vm.stack.

Require ethereum.paris.vm.simulations.proofs.__init__.
Module Evm := __init__.Evm.

Import Run.

Module PopLocals.
  Record t : Set := {
    (* The stack is a pointer to some data in the heap. *)
    stack : unit;
  }.

  Definition init (evm : Evm.t) : t :=
    {|
      stack := tt;
    |}.

  Definition to_object (locals : t) : Object.t Value.t :=
    Object.make_option [
      ("stack", Some Evm.stack_to_value)
    ].
End PopLocals.

Lemma run_pop (stack : Stack.t) (heap : Heap.t) :
  let evm := Heap.to_evm heap in
  let '(result, evm') := StateError.lift_lens Evm.Lens.stack simulations.stack.pop evm in
  let result :=
    match result with
    | inl s' => inl Constant.None_
    | inr exn => inr (Exception.Raise (Some Constant.None_))
    end in
  exists fresh_stack heap',
  {{ stack, heap |
    stack.pop (make_list [Evm.stack_to_value]) (make_dict []) ⇓
    result
  | stack ++ fresh_stack, heap' }} /\
  evm' = Heap.to_evm heap'.
Proof.
  intros.
  destruct StateError.lift_lens as [result evm'] eqn:?.
  unfold stack.pop, simulations.stack.pop in *.
  cbn in *.
  repeat eexists.
  { apply (Run.CallPrimitiveStateAllocStack (PopLocals.init evm) PopLocals.to_object). {
      reflexivity.
    }
    cbn.
    eapply Run.CallPrimitiveStateReadStack. {
      erewrite Stack.read_length_eq.
      reflexivity.
    }
    cbn.
    eapply Run.CallPrimitiveGetInGlobals. {
      apply builtins_is_imported.
      admit.
    }
    admit.
  }
Admitted.
