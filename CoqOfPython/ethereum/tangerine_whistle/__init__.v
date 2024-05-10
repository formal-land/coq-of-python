Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.tangerine_whistle.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
The Tangerine Whistle fork is the first of two forks responding to a
denial-of-service attack on the Ethereum network. It tunes the price of various
EVM instructions, and reduces the state size by removing a number of empty
accounts.
".

Axiom ethereum_fork_criteria_imports :
  AreImported globals "ethereum.fork_criteria" [ "ByBlockNumber" ].

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 2463000
    ],
    make_dict []
  |)
)).
