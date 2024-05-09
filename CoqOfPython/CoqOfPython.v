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
  | Bool (b : bool)
  | Integer (z : Z)
  | String (s : string)
  | Tuple (items : list Value)
  (** Lists and tuples are very similar. The distinction between the two is conventional. We use
      a list when the number of elements is not statically known. *)
  | List (items : list Value)
  | Closure {Value M : Set} (f : list Value -> M)
  | Klass {Value M : Set}
    (bases : list (Set * string))
    (class_methods : list (string * (list Value -> nat -> M)))
    (methods : list Value).
  Arguments Bool {_}.
  Arguments Integer {_}.
  Arguments String {_}.
  Arguments Tuple {_}.
  Arguments List {_}.
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
  Inductive t (Value : Set) : Set :=
  | Imm (data : Object.t Value)
  | Mutable {Address A : Set} (address : Address) (to_data : A -> Object.t Value).
  Arguments Imm {_}.
  Arguments Mutable {_ _ _}.
End Pointer.

Module Value.
  Inductive t : Set :=
  | Make (globals : Set) (klass : string) (value : Pointer.t t).
End Value.

Parameter M : Set.

Parameter IsInGlobals : Set -> Value.t -> string -> Prop.

Definition IsGlobalAlias (globals required_globals : Set) (name : string) : Prop :=
  forall (value : Value.t),
    IsInGlobals required_globals value name ->
    IsInGlobals globals value name.

Module M.
  Parameter pure : Value.t -> M.

  Parameter let_ : M -> (Value.t -> M) -> M.

  Parameter call : Value.t -> list Value.t -> M.

  Parameter get_field : Value.t -> string -> M.

  Parameter get_name : Set -> nat -> string -> M.

  Parameter set_locals : nat -> list (string * Value.t) -> M.

  Parameter return_ : Value.t -> M.

  Parameter impossible : M.

  Parameter run : M -> Value.t.

  Module Notations.
    Notation "e (| e1 , .. , en |)" :=
      (run ((.. (e e1) ..) en))
      (at level 100).

    Notation "e (||)" :=
      (run e)
      (at level 100).
  End Notations.

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

Parameter Inherit : Set -> Set -> Prop.

Module BoolOp.
  Parameter and : Value.t -> M -> M.

  Parameter or : Value.t -> M -> M.
End BoolOp.

Module BinOp.
  Parameter add : Value.t -> Value.t -> M.

  Parameter sub : Value.t -> Value.t -> M.

  Parameter mult : Value.t -> Value.t -> M.

  Parameter matmult : Value.t -> Value.t -> M.

  Parameter div : Value.t -> Value.t -> M.

  Parameter mod_ : Value.t -> Value.t -> M.

  Parameter pow : Value.t -> Value.t -> M.

  Parameter lshift : Value.t -> Value.t -> M.

  Parameter rshift : Value.t -> Value.t -> M.

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
  Inductive globals : Set :=.

  Definition make_klass
    (bases : list (Set * string))
    (class_methods : list (string * (list Value.t -> nat -> M)))
    (methods : list Value.t) :
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

  Definition bool (b : bool) : Value.t :=
    Value.Make builtins.globals "bool" (Pointer.Imm (Object.wrapper (Data.Bool b))).

  Definition int (z : Z) : Value.t :=
    Value.Make builtins.globals "int" (Pointer.Imm (Object.wrapper (Data.Integer z))).

  Definition str (s : string) : Value.t :=
    Value.Make builtins.globals "str" (Pointer.Imm (Object.wrapper (Data.String s))).
End Constant.
