Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Paris fork transitions Ethereum from a proof-of-work consensus model to a
proof-of-stake one. This fork is often referred to as """The Merge""" because it
marks the integration of the [consensus layer] with the execution layer
(defined in this project.)

[consensus layer]: https://github.com/ethereum/consensus-specs
".

Require ethereum.fork_criteria.
Axiom ethereum_fork_criteria_ByBlockNumber :
  IsGlobalAlias globals ethereum.fork_criteria.globals "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 15537394
    ],
    make_dict []
  |)
)).
