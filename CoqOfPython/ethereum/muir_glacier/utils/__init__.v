Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.muir_glacier.utils.__init__".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Utility functions unique to this particular fork.
".
