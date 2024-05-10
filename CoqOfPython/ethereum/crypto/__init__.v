Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.crypto.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
Cryptographic primitives used in Ethereum.
".
