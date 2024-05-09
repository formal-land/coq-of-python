Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Constantinople fork reduces mining rewards, delays the difficulty bomb,
and introduces new EVM instructions for logical shifts, counterfactual
contract deployment, and computing bytecode hashes.
".

Require ethereum.fork_criteria.
Axiom ethereum_fork_criteria_ByBlockNumber :
  IsGlobalAlias globals ethereum.fork_criteria.globals "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 7280000
    ],
    make_dict []
  |)
)).
