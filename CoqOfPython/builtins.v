Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "builtins".

Definition locals_stack : list Locals.t := [].

Definition type : Value.t :=
  make_klass {|
    Klass.bases := [];
    Klass.class_methods := [];
    Klass.methods := [];
  |}.
Axiom type_in_globals : IsInGlobals "builtins" "type" type.

Definition int : Value.t :=
  make_klass {|
    Klass.bases := [];
    Klass.class_methods := [];
    Klass.methods := [];
  |}.
Axiom int_in_globals : IsInGlobals "builtins" "int" int.

Definition str : Value.t :=
  make_klass {|
    Klass.bases := [];
    Klass.class_methods := [];
    Klass.methods := [];
  |}.
Axiom str_in_globals : IsInGlobals "builtins" "str" str.

Definition len : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "value" ] in
    let* value := M.get_name globals locals_stack "value" in
    let '(Value.Make _ _ pointer) := value in
    let- object := M.read pointer in
    match object.(Object.internal) with
    | Some (Data.List list) => M.pure (Constant.int (Z.of_nat (List.length list)))
    | _ => M.impossible
    end.
Axiom len_in_globals : IsInGlobals globals "len" (make_function len).
