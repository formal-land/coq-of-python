Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "builtins".

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

Parameter len : Value.t -> Value.t -> M.
Axiom len_in_globals : IsInGlobals globals "len" (make_function len).
