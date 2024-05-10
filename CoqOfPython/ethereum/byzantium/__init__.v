Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.byzantium.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
The Byzantium fork reduces the mining rewards, delays the difficulty bomb,
lets contracts make non-state-changing calls to other contracts, and adds
cryptographic primitives for layer 2 scaling.
".

Axiom ethereum_fork_criteria_imports_ByBlockNumber :
  IsImported globals "ethereum.fork_criteria" "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByBlockNumber" |),
    make_list [
      Constant.int 4370000
    ],
    make_dict []
  |)
)).
