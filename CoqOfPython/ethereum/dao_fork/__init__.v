Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.dao_fork.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
The DAO Fork is a response to a smart contract exploit known as the 2016 DAO
Attack where a vulnerable contract was drained of its ether. This fork recovers
the stolen funds into a new contract.
".

Axiom ethereum_fork_criteria_imports :
  AreImported globals "ethereum.fork_criteria" [ "ByBlockNumber" ].

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 1920000
    ],
    make_dict []
  |)
)).
