Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.shanghai.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
The Shanghai fork brings staking withdrawals to the execution layer, adds a
push-zero EVM instruction, limits the maximum size of initialization
bytecode, and deprecates the self-destruct EVM instruction.
".

Axiom ethereum_fork_criteria_imports :
  AreImported globals "ethereum.fork_criteria" [ "ByTimestamp" ].

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByTimestamp" |),
    make_list [
      Constant.int 1681338455
    ],
    make_dict []
  |)
)).
