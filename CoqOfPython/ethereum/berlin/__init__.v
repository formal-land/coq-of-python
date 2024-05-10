Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.berlin.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
The Berlin fork adjusts the gas costs of the `ModExp` precompile and several
state access EVM instructions, introduces typed transaction envelopes along
with the first new transaction type—optional access lists.
".

Axiom ethereum_fork_criteria_imports_ByBlockNumber :
  IsImported globals "ethereum.fork_criteria" "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 12244000
    ],
    make_dict []
  |)
)).
