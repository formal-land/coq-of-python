Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.constantinople.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
The Constantinople fork reduces mining rewards, delays the difficulty bomb,
and introduces new EVM instructions for logical shifts, counterfactual
contract deployment, and computing bytecode hashes.
".

Axiom ethereum_fork_criteria_imports :
  AreImported globals "ethereum.fork_criteria" [ "ByBlockNumber" ].

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 7280000
    ],
    make_dict []
  |)
)).
