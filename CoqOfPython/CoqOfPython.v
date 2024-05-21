Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export CoqOfPython.RecordUpdate.

Require Export Lia.
From Hammer Require Export Tactics.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.

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

Module Dict.
  Definition t (Value : Set) : Set :=
    list (string * Value).

  Fixpoint read {Value : Set} (dict : t Value) (key : string) : option Value :=
    match dict with
    | [] => None
    | (current_key, value) :: dict =>
      if String.eqb current_key key then
        Some value
      else
        read dict key
    end.

  Fixpoint update {Value : Set} (dict : t Value) (key : string) (value : Value) : t Value :=
    match dict with
    | [] => []
    | (current_key, current_value) :: dict =>
      if String.eqb current_key key then
        (current_key, value) :: dict
      else
        (current_key, current_value) :: update dict key value
    end.

  (** Starting from Python 3.7 the ordering in `dict` is guaranted to follow the insersion order. *)
  Definition write {Value : Set} (dict : t Value) (key : string) (value : Value) : t Value :=
    match read dict key with
    | Some _ => update dict key value
    | None => dict ++ [(key, value)]
    end.
End Dict.

Module Globals.
  Definition t : Set := string.
End Globals.

Module Klass.
  Record t {Value M : Set} : Set := {
    bases : list (Globals.t * string);
    class_methods : list (string * (Value -> Value -> M));
    methods : list (string * (Value -> Value -> M));
  }.
  Arguments t : clear implicits.
End Klass.

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
  | Dict (dict : Dict.t Value)
  | Closure {Value M : Set} (f : Value -> Value -> M)
  | Klass {Value M : Set} (klass : Klass.t Value M).
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
    fields : Dict.t Value;
  }.
  Arguments t : clear implicits.
  Arguments Build_t {_}.

  Fixpoint fields_of_dict_option {Value : Set} (optional_dict : list (string * option Value)) :
      Dict.t Value :=
    match optional_dict with
    | [] => []
    | (name, Some value) :: optional_dict =>
      Dict.write (fields_of_dict_option optional_dict) name value
    | (_, None) :: optional_dict => fields_of_dict_option optional_dict
    end.

  Definition make_option {Value : Set} (optional_dict : list (string * option Value)) : t Value :=
    {|
      internal := None;
      fields := fields_of_dict_option optional_dict;
    |}.

  Fixpoint fields_of_dict {Value : Set} (dict : list (string * Value)) : Dict.t Value :=
    match dict with
    | [] => []
    | (name, value) :: dict =>
      Dict.write (fields_of_dict dict) name value
    end.

  Definition make {Value : Set} (dict : list (string * Value)) : t Value :=
    {|
      internal := None;
      fields := fields_of_dict dict;
    |}.

  (** When an object is just a wrapper around the [Data.t] type. *)
  Definition wrapper {Value : Set} (data : Data.t Value) : t Value :=
    {|
      internal := Some data;
      fields := [];
    |}.

  Definition empty {Value : Set} : t Value :=
    {|
      internal := None;
      fields := [];
    |}.
End Object.

Module Pointer.
  Module Mutable.
    Module Kind.
      Inductive t : Set :=
      | Stack (index : nat)
      | Heap {Address : Set} (address : Address).
    End Kind.

    Inductive t (Value : Set) : Set :=
    | Make {A : Set} (kind : Kind.t) (to_object : A -> Object.t Value).
    Arguments Make {_ _}.
  End Mutable.

  Inductive t (Value : Set) : Set :=
  | Imm (data : Object.t Value)
  | Mutable (mutable : Mutable.t Value).
  Arguments Imm {_}.
  Arguments Mutable {_}.

  Definition stack {Value A : Set} (index : nat) (to_object : A -> Object.t Value) : t Value :=
    Mutable (Mutable.Make (Mutable.Kind.Stack index) to_object).

  Definition heap {Value A Address : Set} (address : Address) (to_object : A -> Object.t Value) :
      t Value :=
    Mutable (Mutable.Make (Mutable.Kind.Heap address) to_object).
End Pointer.

Module Value.
  Inductive t : Set :=
  | Make (globals : Globals.t) (klass : string) (value : Pointer.t t).
End Value.

Module Locals.
  Definition t : Set := Pointer.t Value.t.
End Locals.

(** ** Constants *)
Module Constant.
  Definition None_ : Value.t :=
    Value.Make "builtins" "NoneType" (Pointer.Imm Object.empty).

  Definition ellipsis : Value.t :=
    Value.Make "builtins" "ellipsis" (Pointer.Imm (Object.wrapper Data.Ellipsis)).

  Definition bool (b : bool) : Value.t :=
    Value.Make "builtins" "bool" (Pointer.Imm (Object.wrapper (Data.Bool b))).

  Definition int (z : Z) : Value.t :=
    Value.Make "builtins" "int" (Pointer.Imm (Object.wrapper (Data.Integer z))).

  Definition float (f : string) : Value.t :=
    Value.Make "builtins" "float" (Pointer.Imm (Object.wrapper (Data.Float f))).

  Definition str (s : string) : Value.t :=
    Value.Make "builtins" "str" (Pointer.Imm (Object.wrapper (Data.String s))).

  Definition bytes (b : string) : Value.t :=
    Value.Make "builtins" "bytes" (Pointer.Imm (Object.wrapper (Data.String b))).
End Constant.

Definition make_tuple (items : list Value.t) : Value.t :=
  Value.Make "builtins" "tuple" (Pointer.Imm (Object.wrapper (Data.Tuple items))).

Definition make_list (items : list Value.t) : Value.t :=
  Value.Make "builtins" "list" (Pointer.Imm (Object.wrapper (Data.List items))).

Definition make_set (items : list Value.t) : Value.t :=
  Value.Make "builtins" "set" (Pointer.Imm (Object.wrapper (Data.Set_ items))).

Parameter order_dict : list (string * Value.t) -> list (string * Value.t).

Definition make_dict (dict : list (string * Value.t)) : Value.t :=
  Value.Make "builtins" "dict" (Pointer.Imm (Object.wrapper (Data.Dict (order_dict dict)))).

Module Primitive.
  Inductive t : Set -> Set :=
  | StateAlloc (object : Object.t Value.t) : t (Pointer.t Value.t)
  | StateRead (mutable : Pointer.Mutable.t Value.t) : t (Object.t Value.t)
  | StateWrite (mutable : Pointer.Mutable.t Value.t) (update : Object.t Value.t) : t unit
  | GetInGlobals (globals : Globals.t) (name : string) : t Value.t.
End Primitive.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (a : A)
  | CallPrimitive {B : Set} (primitive : Primitive.t B) (k : B -> t A)
  | CallClosure {B : Set} (closure : Data.t Value.t) (args kwargs : Value.t) (k : B -> t A)
  | Impossible.
  Arguments Pure {_}.
  Arguments CallPrimitive {_ _}.
  Arguments CallClosure {_ _}.
  Arguments Impossible {_}.

  Fixpoint bind {A B : Set} (e1 : t A) (e2 : A -> t B) : t B :=
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

Parameter IsInGlobals : Globals.t -> string -> Value.t -> Prop.

Definition IsImported (globals : Globals.t) (import : Globals.t) (name : string) : Prop :=
  forall (value : Value.t),
    IsInGlobals import name value ->
    IsInGlobals globals name value.

(** The `builtins` module is accessible from anywhere. *)
Axiom builtins_is_imported :
  forall (globals : Globals.t) (name : string),
  IsImported globals "builtins" name.

Module M.
  Definition pure (v : Value.t) : M :=
    LowM.Pure (inl v).

  Definition bind (e1 : M) (e2 : Value.t -> M) : M :=
    LowM.bind e1 (fun v => match v with
    | inl v => e2 v
    | inr e => LowM.Pure (inr e)
    end).

  Definition impossible : M :=
    LowM.Impossible.

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
  Import Notations.

  Definition call_primitive {A : Set} (primitive : Primitive.t A) : LowM.t A :=
    LowM.CallPrimitive primitive LowM.Pure.

  Definition get_object (value : Value.t) : LowM.t (Object.t Value.t) :=
    let 'Value.Make _ _ pointer := value in
    match pointer with
    | Pointer.Imm obj =>
      LowM.Pure obj
    | Pointer.Mutable mutable => call_primitive (Primitive.StateRead mutable)
    end.

  Definition call (f : Value.t) (args kwargs : Value.t) : M :=
    let- f_object := get_object f in
    match f_object.(Object.internal) with
    | Some f => LowM.CallClosure f args kwargs LowM.Pure
    | None => LowM.Impossible
    end.

  Definition get_field (value : Value.t) (field : string) : M :=
    let- obj := get_object value in
    match Dict.read obj.(Object.fields) field with
    | Some value => pure value
    | None => impossible
    end.

  (** For the `x[i]` syntax. *)
  Definition get_subscript (value : Value.t) (key : Value.t) : M :=
    let* __getitem__ := get_field value "__getitem__" in
    call __getitem__ (make_tuple [key]) (make_dict []).

  Parameter slice : Value.t -> Value.t -> Value.t -> Value.t -> M.

  Definition read (pointer : Pointer.t Value.t) : LowM.t (Object.t Value.t) :=
    match pointer with
    | Pointer.Imm object => LowM.Pure object
    | Pointer.Mutable mutable => call_primitive (Primitive.StateRead mutable)
    end.

  Fixpoint get_name_in_locals_stack
      (locals_stack : list Locals.t)
      (name : string) :
      LowM.t (option Value.t) :=
    match locals_stack with
    | [] => LowM.Pure None
    | locals :: locals_stack =>
      let- locals_object := read locals in
      match Dict.read locals_object.(Object.fields) name with
      | Some value => LowM.Pure (Some value)
      | None => get_name_in_locals_stack locals_stack name
      end
    end.

  Definition get_name (globals : Globals.t) (locals_stack : list Locals.t) (name : string) : M :=
    let- value_in_locals_stack := get_name_in_locals_stack locals_stack name in
    match value_in_locals_stack with
    | Some value => pure value
    | None =>
      let- value := call_primitive (Primitive.GetInGlobals globals name) in
      pure value
    end.

  Fixpoint fields_of_args (args_values : list Value.t) (arg_names : list string) : Dict.t Value.t :=
    match args_values, arg_names with
    | value :: args_values, name :: arg_names =>
      Dict.write (fields_of_args args_values arg_names) name value
    | _, _ => []
    end.

  Definition create_locals
      (locals_stack : list Locals.t)
      (args kwargs : Value.t)
      (arg_names : list string) :
      LowM.t (list Locals.t) :=
    let- args_object := get_object args in
    let- args_values :=
      match args_object.(Object.internal) with
      | Some (Data.List arg_values) => LowM.Pure arg_values
      | _ => LowM.Impossible
      end in
    let- new_locals := call_primitive (Primitive.StateAlloc {|
      Object.internal := None;
      Object.fields := fields_of_args args_values arg_names;
    |}) in
    LowM.Pure (new_locals :: locals_stack).

  Parameter assign : Value.t -> Value.t -> M.

  Parameter assign_local : string -> Value.t -> M.

  Parameter assign_op : (Value.t -> Value.t -> M) -> Value.t -> Value.t -> M.

  Parameter assign_op_local : (Value.t -> Value.t -> M) -> string -> Value.t -> M.

  Parameter delete : Value.t -> M.

  Definition return_ (value : Value.t) : M :=
    LowM.Pure (inr (Exception.Return value)).

  Parameter pass : M.

  Parameter break : M.

  Parameter continue : M.

  Parameter raise : option Value.t -> M.

  Parameter assert : Value.t -> M.

  Definition catch_return (m : M) : M :=
    let- v := m in
    match v with
    | inl v => pure v
    | inr (Exception.Return v) => pure v
    | inr e => LowM.Pure (inr e)
    end.

  Parameter if_then_else : Value.t -> M -> M -> M.

  Parameter for_ : Value.t -> Value.t -> M -> M -> M.

  Parameter while : Value.t -> M -> M -> M.

  (** A tactic that replaces all [M.run] markers with a bind operation.
      This allows to represent Rust programs without introducing
      explicit names for all intermediate computation results. *)
  Ltac monadic e :=
    lazymatch e with
    | context ctxt [let v : _ := ?x in @?f v] =>
      refine (bind _ _);
        [ monadic x
        | let v' := fresh v in
          intro v';
          let y := (eval cbn beta in (f v')) in
          lazymatch context ctxt [let v := x in y] with
          | let _ := x in y => monadic y
          | _ =>
            refine (bind _ _);
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
        refine (bind _ _);
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

Parameter make_list_concat : list Value.t -> M.

Definition make_function (f : Value.t -> Value.t -> M) : Value.t :=
  Value.Make "builtins" "function" (Pointer.Imm (Object.wrapper (Data.Closure f))).

Definition make_klass (klass : Klass.t Value.t M) : Value.t :=
  Value.Make "builtins" "type" (Pointer.Imm (Object.wrapper (Data.Klass klass))).
