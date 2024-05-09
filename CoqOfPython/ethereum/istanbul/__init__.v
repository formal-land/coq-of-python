Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Istanbul fork makes changes to the gas costs of EVM instructions and data,
adds a cryptographic primitive, and introduces an instruction to fetch the
current chain identifier.
".

Require ethereum.fork_criteria.
Axiom ethereum_fork_criteria_ByBlockNumber :
  IsGlobalAlias globals ethereum.fork_criteria.globals "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 9069000
    ],
    make_dict []
  |)
)).
