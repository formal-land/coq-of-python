Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Muir Glacier fork delays the difficulty bomb. There are no other changes
in this fork.
".

Require ethereum.fork_criteria.
Axiom ethereum_fork_criteria_ByBlockNumber :
  IsGlobalAlias globals ethereum.fork_criteria.globals "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 9200000
    ],
    make_dict []
  |)
)).
