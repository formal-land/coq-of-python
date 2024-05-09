Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Spurious Dragon fork is the second of two forks responding to a
denial-of-service attack on the Ethereum network. It tunes the prices of EVM
instructions, adds protection against replaying transaction on different
chains, limits the maximum size of contract code, and enables the removal of
empty accounts.
".

Require ethereum.fork_criteria.
Axiom ethereum_fork_criteria_ByBlockNumber :
  IsGlobalAlias globals ethereum.fork_criteria.globals "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 2675000
    ],
    make_dict []
  |)
)).