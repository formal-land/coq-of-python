Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.crypto.__init__".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Cryptographic primitives used in Ethereum.
".
