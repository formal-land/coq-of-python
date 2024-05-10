Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.frontier.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
Frontier is the first production-ready iteration of the Ethereum protocol.
".

Axiom ethereum_fork_criteria_imports_ByBlockNumber :
  IsImported globals "ethereum.fork_criteria" "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 0
    ],
    make_dict []
  |)
)).
