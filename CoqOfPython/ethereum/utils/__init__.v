Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.utils.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
Utility functions used in this specification.
".
