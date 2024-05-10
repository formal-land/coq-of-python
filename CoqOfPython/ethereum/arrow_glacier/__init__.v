Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.arrow_glacier.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
The Arrow Glacier fork delays the difficulty bomb. There are no other changes
in this fork.
".

Axiom ethereum_fork_criteria_imports_ByBlockNumber :
  IsImported globals "ethereum.fork_criteria" "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 13773000
    ],
    make_dict []
  |)
)).
