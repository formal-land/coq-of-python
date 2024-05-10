Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.london.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
The London fork overhauls the transaction fee market, changes gas refunds,
reserves a contract prefix for future use, and delays the difficulty bomb.
".

Axiom ethereum_fork_criteria_imports :
  AreImported globals "ethereum.fork_criteria" [ "ByBlockNumber" ].

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 12965000
    ],
    make_dict []
  |)
)).
