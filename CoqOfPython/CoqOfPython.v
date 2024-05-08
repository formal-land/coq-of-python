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

Inductive sigS {A : Type} (P : A -> Set) : Set :=
| existS : forall (x : A), P x -> sigS P.
Arguments existS {_ _}.

Reserved Notation "{ x @ P }" (at level 0, x at level 99).
Reserved Notation "{ x : A @ P }" (at level 0, x at level 99).
Reserved Notation "{ ' pat : A @ P }"
  (at level 0, pat strict pattern, format "{ ' pat : A @ P }").

Notation "{ x @ P }" := (sigS (fun x => P)) : type_scope.
Notation "{ x : A @ P }" := (sigS (A := A) (fun x => P)) : type_scope.
Notation "{ ' pat : A @ P }" := (sigS (A := A) (fun pat => P)) : type_scope.

Module Value.
  Inductive t : Set :=
  | OfTy (globals : Set) (klass : string) (value : t)
  | None
  | Bool (b : bool)
  | Integer (z : Z)
  | String (s : string)
  | Tuple (items : list t)
  (** Lists and tuples are very similar. The disctinction between the two is conventional. We use
      a list when the number of elements is not statically known. *)
  | List (items : list t)
  | Closure (f : { '(t, M) : Set * Set @ list t -> M })
  | Klass (bases : list (Set * string)) (class_methods : list t) (methods : list t).
End Value.

Parameter M : Set.

Parameter IsInGlobals : Set -> Value.t -> string -> Prop.

Parameter IsGlobalAlias : Set -> Set -> string -> Prop.

Module M.
  Parameter pure : Value.t -> M.

  Parameter let_ : M -> (Value.t -> M) -> M.

  Parameter call : Value.t -> list Value.t -> M.

  Definition closure (f : list Value.t -> M) : Value.t :=
    Value.Closure (existS (Value.t, M) f).

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

  Definition type : Value.t :=
    Value.OfTy globals "type" (Value.Klass [] [] []).

  Inductive int : Set :=.
End builtins.

(** ** Code example *)

Inductive globals : Set :=.

Parameter foo : list Value.t -> M.

Axiom foo_in_global_names : IsInGlobals globals (M.closure foo) "foo".
