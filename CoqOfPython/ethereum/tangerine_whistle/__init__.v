Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Tangerine Whistle fork is the first of two forks responding to a
denial-of-service attack on the Ethereum network. It tunes the price of various
EVM instructions, and reduces the state size by removing a number of empty
accounts.
".

Require ethereum.fork_criteria.
Axiom ethereum_fork_criteria_ByBlockNumber :
  IsGlobalAlias globals ethereum.fork_criteria.globals "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 2463000
    ],
    make_dict []
  |)
)).
