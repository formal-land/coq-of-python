Require Import CoqOfPython.CoqOfPython.
Require Import simulations.proofs.CoqOfPython.
Require Import simulations.proofs.heap.

Require ethereum.paris.vm.simulations.stack.
Require ethereum.paris.vm.stack.
Require CoqOfPython.builtins.

Require ethereum.paris.vm.simulations.proofs.__init__.
Require simulations.proofs.builtins.

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

(** Test function to experiment with the simulations. We might remove it later. *)
Definition get_length : Value.t -> Value.t -> M :=
  let globals := "ethereum.paris.vm.stack" in
  let locals_stack := [] in

  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    M.catch_return ltac:(M.monadic (
    let _ := Constant.str "
    Returns the length of the stack.
 
    Parameters
    ----------
    evm :
        EVM stack.
 
    Returns
    -------
    length : `int`
        Length of the stack.
 
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "len" |),
        make_list [
          M.get_name (| globals, locals_stack, "evm" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
 
(** Run for the function [get_length]. *)
Definition run_get_length (stack : Stack.t) (heap : Heap.t) :
  {{ stack, heap |
    stack.get_length (make_list [Evm.stack_to_value]) (make_dict []) ⇓
    (fun (n : Z) => inl (Constant.int n))
  |
    fun stack' => stack' = stack,
    fun heap' => heap' = heap
  }}.
Proof.
  cbn.
  apply Run.CallPrimitiveStateAllocImm.
  cbn.
  eapply Run.CallPrimitiveGetInGlobals. {
    apply builtins_is_imported.
    apply builtins.len_in_globals.
  }
  cbn.
  eapply Run.CallClosure. {
    eapply builtins.run_len.
    { pose proof (H := IsRead.Heap stack heap Address.stack).
      now apply H.
    }
    { reflexivity. }
  }
  intros.
  cbn.
  now eapply Run.Pure.
Defined.

(** Very simple version of the function [get_length], that actually only return the length of the
    stack. *)
Definition simple_get_length (heap : Heap.t) : Z :=
  Z.of_nat (List.length heap.(Heap.stack)).

(** We can show that it only returns the length of the stack by reflexivity! *)
Lemma simple_get_length_eq stack heap :
  simple_get_length heap =
  let '(l, _, _) := evaluate (run_get_length stack heap) in
  l.
Proof.
  reflexivity.
Qed.

(** Test module for demo purposes that could be removed later. *)
Module TestGetLength.
  (** Dummy value used for the compute below. *)
  Definition dummy_heap : Heap.t := {|
    Heap.evm := {|
      Heap.Evm.pc := Uint.Make 12;
      Heap.Evm.gas_left := Uint.Make 23;
    |};
    Heap.stack := [
      U256.of_Z 42;
      U256.of_Z 43;
      U256.of_Z 44
    ];
  |}.

  Definition current_length : Z :=
    let '(l, _, _) := evaluate (run_get_length [] dummy_heap) in
    l.

  (* Should return 3 *)
  (* Compute current_length. *)
End TestGetLength.

(** Run of the [pop] function. *)
Definition run_pop (stack : Stack.t) (heap : Heap.t) :
  {{ stack, heap |
    stack.pop (make_list [Evm.stack_to_value]) (make_dict []) ⇓
    (fun (result : unit + builtins.Exception.t) =>
      match result with
      | inl tt => inl Constant.None_
      | inr exn => inr (Exception.Raise (Some (builtins.Exception.to_value exn)))
      end)
  |
    fun stack' => exists fresh_stack, stack' = stack ++ fresh_stack,
    fun heap' => True
  }}.
Proof.
  cbn.
  apply Run.CallPrimitiveStateAllocImm.
  cbn.
  eapply Run.CallPrimitiveGetInGlobals. {
    apply builtins_is_imported.
    apply builtins.len_in_globals.
  }
  cbn.
  eapply Run.CallClosure. {
    eapply builtins.run_len.
    { pose proof (H := IsRead.Heap stack heap Address.stack).
      now apply H.
    }
    { reflexivity. }
  }
  intros.
  cbn.
  replace (Compare.eq (Constant.int value_inter) (Constant.int 0))
    with (M.pure (Constant.bool (value_inter =? 0)))
    by admit.
  cbn.
  match goal with
  | |- context [ M.if_then_else (Constant.bool ?cond) ] =>
    replace (M.if_then_else (Constant.bool cond))
      with (fun (success error : M) => if cond then success else error)
      by admit
  end.
  destruct (_ =? _); cbn.
  { admit. }
  { eapply Run.CallPrimitiveStateRead. {
      pose proof (H2 := IsRead.Heap stack_inter heap_inter Address.stack).
      now apply H2.
    }
    cbn.
    (* TODO: implement method calls *)
    admit.
  }
Admitted.
