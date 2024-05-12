Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.paris.__init__".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
The Paris fork transitions Ethereum from a proof-of-work consensus model to a
proof-of-stake one. This fork is often referred to as ""The Merge"" because it
marks the integration of the [consensus layer] with the execution layer
(defined in this project.)

[consensus layer]: https://github.com/ethereum/consensus-specs
".

Axiom ethereum_fork_criteria_imports_ByBlockNumber :
  IsImported globals "ethereum.fork_criteria" "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "ByBlockNumber" |),
    make_list [
      Constant.int 15537394
    ],
    make_dict []
  |)
)).
