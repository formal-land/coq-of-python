Require Import CoqOfPython.CoqOfPython.

Module Stack.
  Definition t : Set :=
    list {A : Set @ A}.

  Definition read : t -> nat -> option {A : Set @ A} :=
    List.nth_error (A := {A : Set @ A}).

  Fixpoint write {A : Set} (stack : t) (index : nat) (value : A) : t :=
    match stack, index with
    | start :: stack, Datatypes.O => (existS A value) :: stack
    | start :: stack, Datatypes.S index => start :: write stack index value
    | [], _ => []
    end.

  Lemma read_length_eq {A : Set} (stack_start stack_end : t) :
    read (stack_start ++ stack_end) (List.length stack_start) =
    read stack_end 0.
  Proof.
    now induction stack_start.
  Qed.
End Stack.

(** The precise type of the heap is provided by the user. We only enforce some consistency
    properties between the read and write operations. *)
Module Heap.
  Class Trait (Heap Address : Set) : Type := {
    get_Set (a : Address) : Set;
    read (a : Address) : Heap -> option (get_Set a);
    alloc_write (a : Address) : Heap -> get_Set a -> option Heap;
  }.

  Module Valid.
    (** A valid heap should behave as map from address to optional values
        of the type given by the address. A value is [None] while not
        allocated, and [Some] once allocated. It is impossible to free
        allocated values. *)
    Record t `(Trait) : Prop := {
      (* [alloc_write] can only fail on new cells *)
      not_allocated (a : Address) (h : Heap) (v : get_Set a) :
        match alloc_write a h v with
        | Some _ => True
        | None => read a h = None
        end;
      same (a : Address) (h : Heap) (v : get_Set a) :
        match alloc_write a h v with
        | Some h => read a h = Some v
        | None => True
        end;
      different (a1 a2 : Address) (h : Heap) (v2 : get_Set a2) :
        a1 <> a2 ->
        match alloc_write a2 h v2 with
        | Some h' => read a1 h' = read a1 h
        | None => True
        end;
        }.
  End Valid.
End Heap.

Module IsAlloc.
  Inductive t `{Heap.Trait}
    (stack : Stack.t) (heap : Heap) :
    Pointer.Mutable.t Value.t ->
    Object.t Value.t ->
    Stack.t -> Heap ->
    Set :=
  | Stack {A : Set} to_object (value : A) object :
    let index := List.length stack in
    object = to_object value ->
    t
      stack heap
      (Pointer.Mutable.Make (Pointer.Mutable.Kind.Stack index) to_object)
      object
      (stack ++ [existS A value]) heap
  | Heap heap' (address : Address) to_object value object :
    Heap.read address heap = None ->
    Heap.alloc_write address heap value = Some heap' ->
    object = to_object value ->
    t
      stack heap
      (Pointer.Mutable.Make (Pointer.Mutable.Kind.Heap address) to_object)
      object
      stack heap'.
  (* We make the first arguments implicit so that we can apply this contructor in proofs directly
     with the parameters than cannot be found by unification, namely [to_object] and [value]. *)
  Arguments Stack {_ _ _ _ _ _}.
End IsAlloc.

Module IsRead.
  Inductive t `{Heap.Trait}
    (stack : Stack.t) (heap : Heap) :
    Pointer.Mutable.t Value.t ->
    Object.t Value.t ->
    Set :=
  | Stack {A : Set} index to_object (value : A) :
    Stack.read stack index = Some (existS A value) ->
    t
      stack heap
      (Pointer.Mutable.Make (Pointer.Mutable.Kind.Stack index) to_object)
      (to_object value)
  | Heap (address : Address) to_object value :
    Heap.read address heap = Some value ->
    t
      stack heap
      (Pointer.Mutable.Make (Pointer.Mutable.Kind.Heap address) to_object)
      (to_object value).
End IsRead.

Module PointerRead.
  (** A generalization of [IsRead.t] to take into account immediate values. Useful for some
      lemma. *)
  Definition t `{Heap.Trait}
      (stack : Stack.t) (heap : Heap)
      (pointer : Pointer.t Value.t)
      (object : Object.t Value.t) :
      Set :=
    match pointer with
    | Pointer.Imm object' => object' = object
    | Pointer.Mutable mutable => IsRead.t stack heap mutable object
    end.
End PointerRead.

Module IsWrite.
  Inductive t `{Heap.Trait}
    (stack : Stack.t) (heap : Heap) :
    Pointer.Mutable.t Value.t ->
    Object.t Value.t ->
    Stack.t -> Heap ->
    Set :=
  | Stack {A : Set} index to_object (update : A) update_object :
    let stack' := Stack.write stack index update in
    update_object = to_object update ->
    t
      stack heap
      (Pointer.Mutable.Make (Pointer.Mutable.Kind.Stack index) to_object)
      update_object
      stack' heap
  | Heap (address : Address) to_object update update_object heap' :
    Heap.alloc_write address heap update = Some heap' ->
    update_object = to_object update ->
    t
      stack heap
      (Pointer.Mutable.Make (Pointer.Mutable.Kind.Heap address) to_object)
      update_object
      stack heap'.
End IsWrite.

Module Run.
  Reserved Notation "{{ stack , heap | e ⇓ to_value | P_stack , P_heap }}".

  (** A execution trace of a monadic expression, where we do name resolution and explicit an
      allocation strategy. We do not talk about the result, we only say that it exists. Thus we can
      infer the result when building the trace rather than stating it beforehand. The [evaluate]
      function defined after can compute this result from a trace. We will make our specifications
      and proofs about the output of the [evaluate] function.

      Even if we do not compute the result, we still constraint it with the [to_value] function,
      saying that it should be in the image of this function, and with the [P_stack] and [P_heap]
      predicates, saying that the stack and heap should respect some properties. This is mainly
      useful for the [CallClosure] case, in order to avoid exploring impossible branches or
      branches corresponding to ill-typed Python expressions at the return of a function call.

      The [P_stack] and [P_heap] predicates should be very simple. The attempt here is not to
      verify the code, only to build an execution trace. It should mainly contain information about
      the size of the stack and the presence of some values in the heap, just enough to be able to
      build the trace.
  *)
  Inductive t `{Heap.Trait} {A B : Set}
      (stack : Stack.t) (heap : Heap)
      (to_value : A -> B) (P_stack : Stack.t -> Prop) (P_heap : Heap -> Prop) :
      LowM.t B -> Set :=
  (** Final case of an execution. We check that [to_value], [P_stack], and [P_heap] are true. *)
  | Pure
    (* We can have some choices for the expression of [result]. One can use [rewrite] in order to
       simplify the [result] expression and provide something that will simplify the proofs later.
    *)
    (result : A)
    (result' : B) :
    result' = to_value result ->
    P_stack stack ->
    P_heap heap ->
    {{ stack, heap |
      LowM.Pure result' ⇓
      to_value
    | P_stack, P_heap }}
  (** Allocation as an immediate value for that values that will not be modified. If the code is
      written in a purely functional way, we should only do immediate allocations. This removes the
      need to manipulate pointers in the proofs later. *)
  | CallPrimitiveStateAllocImm
      (object : Object.t Value.t)
      (k : Pointer.t Value.t -> LowM.t B) :
    {{ stack, heap |
      k (Pointer.Imm object) ⇓
      to_value
    | P_stack, P_heap }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateAlloc object) k ⇓
      to_value
    | P_stack, P_heap }}
  (** Allocation either on the stack or the heap. *)
  | CallPrimitiveStateAllocMutable
      (mutable : Pointer.Mutable.t Value.t)
      (object : Object.t Value.t)
      (stack_inter : Stack.t) (heap_inter : Heap)
      (k : Pointer.t Value.t -> LowM.t B) :
    IsAlloc.t
      stack heap
      mutable
      object
      stack_inter heap_inter ->
    {{ stack_inter, heap_inter |
      k (Pointer.Mutable mutable) ⇓
      to_value
    | P_stack, P_heap }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateAlloc object) k ⇓
      to_value
    | P_stack, P_heap }}
  (** Read of a pointer in the stack or the heap. *)
  | CallPrimitiveStateRead
      (mutable : Pointer.Mutable.t Value.t)
      (object : Object.t Value.t)
      (k : Object.t Value.t -> LowM.t B) :
    IsRead.t stack heap mutable object ->
    {{ stack, heap |
      k object ⇓
      to_value
    | P_stack, P_heap }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateRead mutable) k ⇓
      to_value
    | P_stack, P_heap }}
  (** Read to a pointer in the stack or the heap. *)
  | CallPrimitiveStateWrite
      (mutable : Pointer.Mutable.t Value.t)
      (update : Object.t Value.t)
      (stack_inter : Stack.t) (heap_inter : Heap)
      (k : unit -> LowM.t B) :
    IsWrite.t stack heap mutable update stack_inter heap_inter ->
    {{ stack_inter, heap_inter |
      k tt ⇓
      to_value
    | P_stack, P_heap }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateWrite mutable update) k ⇓
      to_value
    | P_stack, P_heap }}
  (** Name resolution for top-level names. *)
  | CallPrimitiveGetInGlobals
      (globals : Globals.t)
      (name : string)
      (value : Value.t)
      (k : Value.t -> LowM.t B) :
    IsInGlobals globals name value ->
    {{ stack, heap |
      k value ⇓
      to_value
    | P_stack, P_heap }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.GetInGlobals globals name) k ⇓
      to_value
    | P_stack, P_heap }}
  (** Call of a closure. We abstract away the detail of the call. We use closures as an explicit
      abstraction barrier to split our traces. *)
  | CallClosure {C : Set}
      (f : Value.t -> Value.t -> M)
      (args kwargs : Value.t)
      (to_value_inter : C -> Value.t + Exception.t)
      (P_stack_inter : Stack.t -> Prop) (P_heap_inter : Heap -> Prop)
      (k : Value.t + Exception.t -> LowM.t B) :
    let closure := Data.Closure f in
    {{ stack, heap |
      f args kwargs ⇓
      to_value_inter
    | P_stack_inter, P_heap_inter }} ->
    (* We quantify over every possible values as we cannot compute the result of the closure here.
       We only know that it exists and respect some constraints in this inductive definition. *)
    (forall value_inter stack_inter heap_inter,
      P_stack_inter stack_inter ->
      P_heap_inter heap_inter ->
      {{ stack_inter, heap_inter |
        k (to_value_inter value_inter) ⇓
        to_value
      | P_stack, P_heap }}
    ) ->
    {{ stack, heap |
      LowM.CallClosure closure args kwargs k ⇓
      to_value
    | P_stack, P_heap }}

  where "{{ stack , heap | e ⇓ to_value | P_stack , P_heap }}" :=
    (t stack heap to_value P_stack P_heap e).
End Run.

Import Run.

(** Get the value computed from the trace of a monadic expression. We will do our proofs on the
    output of this function, as it gives a purely functional interpretation of the translated
    monadic expressions.

    Do be able to do the induction in this definition, we also return a proof for [P_stack]
    and [P_heap].
*)
Fixpoint evaluate `{Heap.Trait} {A B : Set}
    {stack : Stack.t} {heap : Heap} {e : LowM.t B}
    {to_value : A -> B} {P_stack : Stack.t -> Prop} {P_heap : Heap -> Prop}
    (run : {{ stack, heap | e ⇓ to_value | P_stack, P_heap }}) :
  A *
  { stack : Stack.t | P_stack stack } *
  { heap : Heap | P_heap heap }.
Proof.
  (* We use very explicit tactics in order to make sure that we build the definition we want. *)
  destruct run.
  { repeat split.
    { exact result. }
    { try eexists.
      match goal with
      | H : P_stack _ |- _ => exact H
      end.
    }
    { try eexists.
      match goal with
      | H : P_heap _ |- _ => exact H
      end.
    }
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { destruct (evaluate _ _ _ _ _ _ _ _ _ _ _ run) as
      [[value_inter [stack_inter H_stack_inter]] [heap_inter H_heap_inter]].
    eapply evaluate.
    match goal with
    | H : forall _ _ _, _ |- _ => apply (H value_inter)
    end.
    { exact H_stack_inter. }
    { exact H_heap_inter. }
  }
Defined.

(** Trace of the read at a memory location, wether it is an immediate or allocated value. *)
Definition run_read `{Heap.Trait} {A : Set}
    (stack : Stack.t) (heap : Heap)
    (pointer : Pointer.t Value.t)
    (object : Object.t Value.t)
    (to_value : A -> Value.t + Exception.t)
    (k : Object.t Value.t -> M)
    (P_stack : Stack.t -> Prop) (P_heap : Heap -> Prop)
    (H_pointer : PointerRead.t stack heap pointer object) :
  {{ stack, heap |
    k object ⇓
    to_value
  | P_stack, P_heap }} ->
  {{ stack, heap |
    LowM.bind (M.read pointer) k ⇓
    to_value
  | P_stack, P_heap }}.
Proof.
  intros.
  destruct pointer; cbn in *.
  { congruence. }
  { eapply Run.CallPrimitiveStateRead. {
      apply H_pointer.
    }
    trivial.
  }
Defined.
