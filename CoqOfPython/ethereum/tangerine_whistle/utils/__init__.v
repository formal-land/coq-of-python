Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.tangerine_whistle.utils.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
Utility functions unique to this particular fork.
".
