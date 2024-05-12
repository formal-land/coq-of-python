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

Module Run.
  Reserved Notation "{{ stack , heap | e ⇓ result | stack' , heap' }}".

  Inductive t `{Heap.Trait} {A : Set}
      (* Be aware of the order of parameters: the result and final heap are at
         the beginning. This is due to the way polymorphic types for inductive
         work in Coq, and the fact that the result is always the same as we are
         in continuation passing style. *)
      {result : A} {stack' : Stack.t} {heap' : Heap} :
      LowM.t A -> Stack.t -> Heap -> Prop :=
  | Pure :
    {{ stack', heap' |
      LowM.Pure result ⇓
      result
    | stack', heap' }}
  | CallPrimitiveStateAllocImmediate
      (stack : Stack.t) (heap : Heap) (object : Object.t Value.t)
      (k : Pointer.t Value.t -> LowM.t A) :
    {{ stack, heap |
      k (Pointer.Imm object) ⇓
      result
    | stack', heap' }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateAlloc object) k ⇓
      result
    | stack', heap' }}
  | CallPrimitiveStateAllocStack {B : Set}
      (value : B)
      (to_object : B -> Object.t Value.t)
      (object : Object.t Value.t)
      (stack : Stack.t) (heap : Heap)
      (k : Pointer.t Value.t -> LowM.t A) :
    let stack_inter := (stack ++ [existS B value])%list in
    let index := List.length stack in
    let mutable := Pointer.Mutable.Stack index to_object in
    object = to_object value ->
    {{ stack_inter, heap |
      k (Pointer.Mutable mutable) ⇓
      result
    | stack', heap' }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateAlloc object) k ⇓
      result
    | stack', heap' }}
  | CallPrimitiveStateAllocHeap
      (address : Address)
      (value : Heap.get_Set address)
      (object : Object.t Value.t)
      (to_object : Heap.get_Set address -> Object.t Value.t)
      (stack : Stack.t) (heap heap_inter : Heap)
      (k : Pointer.t Value.t -> LowM.t A) :
    let mutable := Pointer.Mutable.Heap address to_object in
    object = to_object value ->
    Heap.read address heap = None ->
    Heap.alloc_write address heap value = Some heap_inter ->
    {{ stack, heap_inter |
      k (Pointer.Mutable mutable) ⇓
      result
    | stack', heap' }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateAlloc object) k ⇓
      result
    | stack', heap' }}
  | CallPrimitiveStateReadStack {B : Set}
      (index : nat)
      (to_object : B -> Object.t Value.t)
      (value : B)
      (stack : Stack.t) (heap : Heap)
      (k : Object.t Value.t -> LowM.t A) :
    let mutable := Pointer.Mutable.Stack index to_object in
    Stack.read stack index = Some (existS B value) ->
    {{ stack, heap |
      k (to_object value) ⇓
      result
    | stack', heap' }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateRead mutable) k ⇓
      result
    | stack', heap' }}
  | CallPrimitiveStateReadHeap
      (address : Address)
      (to_object : Heap.get_Set address -> Object.t Value.t)
      (value : Heap.get_Set address)
      (stack : Stack.t) (heap : Heap)
      (k : Object.t Value.t -> LowM.t A) :
    let mutable := Pointer.Mutable.Heap address to_object in
    Heap.read address heap = Some value ->
    {{ stack, heap |
      k (to_object value) ⇓
      result
    | stack', heap' }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateRead mutable) k ⇓
      result
    | stack', heap' }}
  | CallPrimitiveStateWriteStack {B : Set}
      (index : nat)
      (to_object : B -> Object.t Value.t)
      (update : B)
      (update' : Object.t Value.t)
      (stack : Stack.t) (heap : Heap)
      (k : unit -> LowM.t A) :
    let stack_inter := Stack.write stack index update in
    let mutable := Pointer.Mutable.Stack index to_object in
    update' = to_object update ->
    {{ stack_inter, heap |
      k tt ⇓
      result
    | stack', heap' }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateWrite mutable update') k ⇓
      result
    | stack', heap' }}
  | CallPrimitiveStateWriteHeap
      (address : Address)
      (to_object : Heap.get_Set address -> Object.t Value.t)
      (update : Heap.get_Set address)
      (update' : Object.t Value.t)
      (stack : Stack.t) (heap heap_inter : Heap)
      (k : unit -> LowM.t A) :
    let mutable := Pointer.Mutable.Heap address to_object in
    update' = to_object update ->
    Heap.alloc_write address heap update = Some heap_inter ->
    {{ stack, heap_inter |
      k tt ⇓
      result
    | stack', heap' }} ->
    {{ stack, heap |
      LowM.CallPrimitive (Primitive.StateWrite mutable update') k ⇓
      result
    | stack', heap' }}
  | CallClosure
      (stack stack_inter : Stack.t) (heap heap_inter : Heap)
      (f : Value.t -> Value.t -> M)
      (args kwargs : Value.t)
      (value : Value.t + Exception.t)
      (k : Value.t + Exception.t -> LowM.t A) :
    let closure := Data.Closure f in
    {{ stack, heap |
      f args kwargs ⇓
      value
    | stack_inter, heap_inter }} ->
    {{ stack_inter, heap_inter |
      k value ⇓
      result
    | stack', heap' }} ->
    {{ stack, heap |
      LowM.CallClosure closure args kwargs k ⇓
      result
    | stack', heap' }}

  where "{{ stack , heap | e ⇓ result | stack' , heap' }}" :=
    (t (result := result) (stack' := stack') (heap' := heap') e stack heap).
End Run.
