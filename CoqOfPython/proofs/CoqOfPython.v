Require Import CoqOfPython.CoqOfPython.

Module State.
  Class Trait (State Address : Set) : Type := {
    get_Set (a : Address) : Set;
    read (a : Address) : State -> option (get_Set a);
    alloc_write (a : Address) : State -> get_Set a -> option State;
  }.

  Module Valid.
    (** A valid state should behave as map from address to optional values
        of the type given by the address. A value is [None] while not
        allocated, and [Some] once allocated. It is impossible to free
        allocated values. *)
    Record t `(Trait) : Prop := {
      (* [alloc_write] can only fail on new cells *)
      not_allocated (a : Address) (s : State) (v : get_Set a) :
        match alloc_write a s v with
        | Some _ => True
        | None => read a s = None
        end;
      same (a : Address) (s : State) (v : get_Set a) :
        match alloc_write a s v with
        | Some s => read a s = Some v
        | None => True
        end;
      different (a1 a2 : Address) (s : State) (v2 : get_Set a2) :
        a1 <> a2 ->
        match alloc_write a2 s v2 with
        | Some s' => read a1 s' = read a1 s
        | None => True
        end;
        }.
  End Valid.
End State.

Module Run.
  Reserved Notation "{{ state | e ⇓ result | state' }}".

  Inductive t `{State.Trait} {A : Set}
      (* Be aware of the order of parameters: the result and final state are at
         the beginning. This is due to the way polymorphic types for inductive
         work in Coq, and the fact that the result is always the same as we are
         in continuation passing style. *)
      (result : A) (state' : State) :
      LowM.t A -> State -> Prop :=
  | Pure :
    {{ state' | LowM.Pure result ⇓ result | state' }}
  | CallPrimitiveStateAllocImmediate
      (state : State) (object : Object.t Value.t)
      (k : Pointer.t Value.t -> LowM.t A) :
    {{ state |
      k (Pointer.Imm object) ⇓ result
    | state' }} ->
    {{ state |
      LowM.CallPrimitive (Primitive.StateAlloc object) k ⇓ result
    | state' }}
  | CallPrimitiveStateAllocMutable
      (address : Address)
      (value : State.get_Set address)
      (object : Object.t Value.t)
      (to_object : State.get_Set address -> Object.t Value.t)
      (state : State)
      (k : Pointer.t Value.t -> LowM.t A) :
    object = to_object value ->
    State.read address state = None ->
    State.alloc_write address state value = Some state' ->
    {{ state |
      k (Pointer.Mutable (Pointer.Mutable.Make address to_object)) ⇓ result
    | state' }} ->
    {{ state |
      LowM.CallPrimitive (Primitive.StateAlloc object) k ⇓ result
    | state' }}
  | CallPrimitiveStateRead
      (address : Address)
      (to_object : State.get_Set address -> Object.t Value.t)
      (value : State.get_Set address)
      (state : State)
      (k : Object.t Value.t -> LowM.t A) :
    let mutable := Pointer.Mutable.Make address to_object in
    State.read address state = Some value ->
    {{ state |
      k (to_object value) ⇓
      result
    | state' }} ->
    {{ state |
      LowM.CallPrimitive (Primitive.StateRead mutable) k ⇓
      result
    | state' }}
  | CallPrimitiveStateWrite
      (address : Address)
      (to_object : State.get_Set address -> Object.t Value.t)
      (update : State.get_Set address)
      (update' : Object.t Value.t)
      (state state_inter : State)
      (k : unit -> LowM.t A) :
    let mutable := Pointer.Mutable.Make address to_object in
    update' = to_object update ->
    State.alloc_write address state update = Some state_inter ->
    {{ state_inter |
      k tt ⇓
      result
    | state' }} ->
    {{ state |
      LowM.CallPrimitive (Primitive.StateWrite mutable update') k ⇓
      result
    | state' }}
  | CallClosure
      (state state_inter : State)
      (f : Value.t -> Value.t -> M)
      (args kwargs : Value.t)
      (value : Value.t + Exception.t)
      (k : Value.t + Exception.t -> LowM.t A) :
    let closure := Data.Closure f in
    {{ state |
      f args kwargs ⇓
      value
    | state_inter }} ->
    {{ state_inter |
      k value ⇓
      result
    | state' }} ->
    {{ state |
      LowM.CallClosure closure args kwargs k ⇓
      result
    | state' }}

  where "{{ state | e ⇓ result | state' }}" :=
    (t result state' e state).
End Run.
