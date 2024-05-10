Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.paris.utils.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
Utility functions unique to this particular fork.
".
