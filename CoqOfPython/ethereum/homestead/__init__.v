Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Homestead fork increases the gas cost of creating contracts, restricts the
range of valid ECDSA signatures for transactions (but not precompiles), tweaks
the behavior of contract creation with insufficient gas, delays the
difficulty bomb, and adds an improved delegate call EVM instruction.
".

Require ethereum.fork_criteria.
Axiom ethereum_fork_criteria_ByBlockNumber :
  IsGlobalAlias globals ethereum.fork_criteria.globals "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 1150000
    ],
    make_dict []
  |)
)).
