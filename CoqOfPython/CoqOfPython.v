Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export CoqOfPython.RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope string_scope.
Global Open Scope Z_scope.
Global Open Scope type_scope.

Export List.ListNotations.

Module Data.
  (** This type is not accessible directly in Python, as only object are. We use this type
      internally to represent integers, closures, ... that can be made accessible in a special
      field of objects. *)
  Inductive t (Value : Set) : Set :=
  | Ellipsis
  | Bool (b : bool)
  | Integer (z : Z)
  | Float (f : string)
  | String (s : string)
  | Tuple (items : list Value)
  (** Lists and tuples are very similar. The distinction between the two is conventional. We use
      a list when the number of elements is not statically known. *)
  | List (items : list Value)
  | Set_ (items : list Value)
  | Dict (dict : list (string * Value))
  | Closure {Value M : Set} (f : Value -> Value -> M)
  | Klass {Value M : Set}
    (bases : list (string * string))
    (class_methods : list (string * (Value -> Value -> M)))
    (methods : list (string * (Value -> Value -> M))).
  Arguments Ellipsis {_}.
  Arguments Bool {_}.
  Arguments Integer {_}.
  Arguments Float {_}.
  Arguments String {_}.
  Arguments Tuple {_}.
  Arguments List {_}.
  Arguments Set_ {_}.
  Arguments Dict {_}.
  Arguments Closure {_ _ _}.
  Arguments Klass {_ _ _}.
End Data.

Module Object.
  Record t {Value : Set} : Set := {
    internal : option (Data.t Value);
    fields : list (string * Value);
  }.
  Arguments t : clear implicits.
  Arguments Build_t {_}.

  (** When an object is just a wrapper around the [Data.t] type. *)
  Definition wrapper {Value : Set} (data : Data.t Value) : t Value :=
    {|
      internal := Some data;
      fields := [];
    |}.
End Object.

Module Pointer.
  Module Mutable.
    Inductive t (Value : Set) : Set :=
    | Make {Address A : Set} (address : Address) (to_object : A -> Object.t Value).
    Arguments Make {_ _ _}.
  End Mutable.

  Inductive t (Value : Set) : Set :=
  | Imm (data : Object.t Value)
  | Mutable (mutable : Mutable.t Value).
  Arguments Imm {_}.
  Arguments Mutable {_}.
End Pointer.

Module Value.
  Inductive t : Set :=
  | Make (globals : string) (klass : string) (value : Pointer.t t).
End Value.

Module Primitive.
  Inductive t : Set -> Set :=
  | StateAlloc (value : Value.t) : t unit
  | StateRead (mutable : Pointer.Mutable.t Value.t) : t (Object.t Value.t)
  | StateWrite (mutable : Pointer.Mutable.t Value.t) (update : Value.t) : t unit.
End Primitive.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (a : A)
  | CallPrimitive {B : Set} (primitive : Primitive.t B) (k : B -> t A)
  | CallClosure (closure : Value.t) (args kwargs : Value.t) (k : A -> t A)
  | Impossible.
  Arguments Pure {_}.
  Arguments CallPrimitive {_ _}.
  Arguments CallClosure {_}.
  Arguments Impossible {_}.

  Fixpoint bind {A : Set} (e1 : t A) (e2 : A -> t A) : t A :=
    match e1 with
    | Pure a => e2 a
    | CallPrimitive primitive k => CallPrimitive primitive (fun v => bind (k v) e2)
    | CallClosure closure args kwargs k => CallClosure closure args kwargs (fun a => bind (k a) e2)
    | Impossible => Impossible
    end.
End LowM.

Module Exception.
  Inductive t : Set :=
  | Return (value : Value.t)
  | Continue
  | Break
  | Raise (value : option Value.t).
End Exception.

Definition M : Set :=
  LowM.t (Value.t + Exception.t).

Parameter IsInGlobals : string -> Value.t -> string -> Prop.

Parameter IsImported : string -> string -> string -> Prop.

Module M.
  Definition pure (v : Value.t) : M :=
    LowM.Pure (inl v).

  Definition bind (e1 : M) (e2 : Value.t -> M) : M :=
    LowM.bind e1 (fun v => match v with
    | inl v => e2 v
    | inr e => LowM.Pure (inr e)
    end).

  (** This axiom is only used as a marker for the [monadic] tactic below, and should not appear in
      the final code of the definitions once the tactic is applied. *)
  Parameter run : M -> Value.t.

  Module Notations.
    Notation "'let-' a := b 'in' c" :=
      (LowM.bind b (fun a => c))
        (at level 200, b at level 100, a name).
  
    Notation "'let*' a := b 'in' c" :=
      (bind b (fun a => c))
        (at level 200, b at level 100, a name).
  
    Notation "'let*' ' a ':=' b 'in' c" :=
      (bind b (fun a => c))
      (at level 200, a pattern, b at level 100, c at level 200).

    Notation "e (| e1 , .. , en |)" :=
      (run ((.. (e e1) ..) en))
      (at level 100).

    Notation "e (| |)" :=
      (run e)
      (at level 100).
  End Notations.

  Definition call (f : Value.t) (args kwargs : Value.t) : M :=
    LowM.CallClosure f args kwargs LowM.Pure.

  Definition get_object (value : Value.t) : LowM.t (Object.t Value.t) :=
    let 'Value.Make _ _ pointer := value in
    match pointer with
    | Pointer.Imm obj =>
      LowM.Pure obj
    | Pointer.Mutable mutable =>
      LowM.CallPrimitive (Primitive.StateRead mutable) LowM.Pure
    end.

  Parameter get_field : Value.t -> string -> M.

  (** For the `x[i]` syntax. *)
  Parameter get_subscript : Value.t -> Value.t -> M.

  Parameter slice : Value.t -> Value.t -> Value.t -> Value.t -> M.

  Parameter get_name : string -> string -> M.

  Parameter set_locals : Value.t -> Value.t -> list string -> M.

  Parameter assign : Value.t -> Value.t -> M.

  Parameter assign_local : string -> Value.t -> M.

  Parameter assign_op : (Value.t -> Value.t -> M) -> Value.t -> Value.t -> M.

  Parameter assign_op_local : (Value.t -> Value.t -> M) -> string -> Value.t -> M.

  Parameter delete : Value.t -> M.

  Parameter return_ : Value.t -> M.

  Parameter pass : M.

  Parameter break : M.

  Parameter continue : M.

  Parameter raise : option Value.t -> M.

  Parameter assert : Value.t -> M.

  Parameter impossible : M.

  Parameter if_then_else : Value.t -> M -> M -> M.

  Parameter for_ : Value.t -> Value.t -> M -> M -> M.

  Parameter while : Value.t -> M -> M -> M.

  (** A tactic that replaces all [M.run] markers with a bind operation.
      This allows to represent Rust programs without introducing
      explicit names for all intermediate computation results. *)
  Ltac monadic e :=
    lazymatch e with
    | context ctxt [let v : _ := ?x in @?f v] =>
      refine (let_ _ _);
        [ monadic x
        | let v' := fresh v in
          intro v';
          let y := (eval cbn beta in (f v')) in
          lazymatch context ctxt [let v := x in y] with
          | let _ := x in y => monadic y
          | _ =>
            refine (let_ _ _);
              [ monadic y
              | let w := fresh "v" in
                intro w;
                let z := context ctxt [w] in
                monadic z
              ]
          end
        ]
    | context ctxt [run ?x] =>
      lazymatch context ctxt [run x] with
      | run x => monadic x
      | _ =>
        refine (let_ _ _);
          [ monadic x
          | let v := fresh "v" in
            intro v;
            let y := context ctxt [v] in
            monadic y
          ]
      end
    | _ =>
      lazymatch type of e with
      | M => exact e
      | _ => exact (pure e)
      end
    end.
End M.

Export M.Notations.

Parameter Inherit : string -> string -> Prop.

Module BoolOp.
  Parameter and : Value.t -> M -> M.

  Parameter or : Value.t -> M -> M.
End BoolOp.

Module BinOp.
  Parameter add : Value.t -> Value.t -> M.

  Parameter sub : Value.t -> Value.t -> M.

  Parameter mult : Value.t -> Value.t -> M.

  Parameter mat_mult : Value.t -> Value.t -> M.

  Parameter div : Value.t -> Value.t -> M.

  Parameter mod_ : Value.t -> Value.t -> M.

  Parameter pow : Value.t -> Value.t -> M.

  Parameter l_shift : Value.t -> Value.t -> M.

  Parameter r_shift : Value.t -> Value.t -> M.

  Parameter bit_or : Value.t -> Value.t -> M.

  Parameter bit_xor : Value.t -> Value.t -> M.

  Parameter bit_and : Value.t -> Value.t -> M.

  Parameter floor_div : Value.t -> Value.t -> M.
End BinOp.

Module UnOp.
  Parameter invert : Value.t -> M.

  Parameter not : Value.t -> M.

  Parameter add : Value.t -> M.

  Parameter sub : Value.t -> M.
End UnOp.

Module Compare.
  Parameter eq : Value.t -> Value.t -> M.

  Parameter not_eq : Value.t -> Value.t -> M.

  Parameter lt : Value.t -> Value.t -> M.

  Parameter lt_e : Value.t -> Value.t -> M.

  Parameter gt : Value.t -> Value.t -> M.

  Parameter gt_e : Value.t -> Value.t -> M.

  Parameter is : Value.t -> Value.t -> M.

  Parameter is_not : Value.t -> Value.t -> M.

  Parameter in_ : Value.t -> Value.t -> M.

  Parameter not_in : Value.t -> Value.t -> M.
End Compare.

(** ** Builtins *)
Module builtins.
  Definition globals : string := "builtins".

  Definition make_klass
    (bases : list (string * string))
    (class_methods : list (string * (Value.t -> Value.t -> M)))
    (methods : list (string * (Value.t -> Value.t -> M))) :
    Value.t :=
  Value.Make builtins.globals "type" (Pointer.Imm (Object.wrapper (
    Data.Klass bases class_methods methods
  ))).

  Definition type : Value.t :=
    make_klass [] [] [].
  Axiom type_in_globals : IsInGlobals globals type "type".

  Definition int : Value.t :=
    make_klass [] [] [].
  Axiom int_in_globals : IsInGlobals globals int "int".

  Definition str : Value.t :=
    make_klass [] [] [].
  Axiom str_in_globals : IsInGlobals globals str "str".
End builtins.

Module Constant.
  Definition None_ : Value.t :=
    Value.Make builtins.globals "NoneType" (Pointer.Imm {|
      Object.internal := None;
      Object.fields := [];
    |}).

  Definition ellipsis : Value.t :=
    Value.Make builtins.globals "ellipsis" (Pointer.Imm (Object.wrapper Data.Ellipsis)).

  Definition bool (b : bool) : Value.t :=
    Value.Make builtins.globals "bool" (Pointer.Imm (Object.wrapper (Data.Bool b))).

  Definition int (z : Z) : Value.t :=
    Value.Make builtins.globals "int" (Pointer.Imm (Object.wrapper (Data.Integer z))).

  Definition float (f : string) : Value.t :=
    Value.Make builtins.globals "float" (Pointer.Imm (Object.wrapper (Data.Float f))).

  Definition str (s : string) : Value.t :=
    Value.Make builtins.globals "str" (Pointer.Imm (Object.wrapper (Data.String s))).

  Definition bytes (b : string) : Value.t :=
    Value.Make builtins.globals "bytes" (Pointer.Imm (Object.wrapper (Data.String b))).
End Constant.

Definition make_tuple (items : list Value.t) : Value.t :=
  Value.Make builtins.globals "tuple" (Pointer.Imm (Object.wrapper (Data.Tuple items))).

Definition make_list (items : list Value.t) : Value.t :=
  Value.Make builtins.globals "list" (Pointer.Imm (Object.wrapper (Data.List items))).

Parameter make_list_concat : list Value.t -> M.

Definition make_set (items : list Value.t) : Value.t :=
  Value.Make builtins.globals "set" (Pointer.Imm (Object.wrapper (Data.Set_ items))).

Parameter order_dict : list (string * Value.t) -> list (string * Value.t).

Definition make_dict (dict : list (string * Value.t)) : Value.t :=
  Value.Make builtins.globals "dict" (Pointer.Imm (Object.wrapper (Data.Dict (order_dict dict)))).
