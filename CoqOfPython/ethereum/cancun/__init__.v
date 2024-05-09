Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Cancun fork introduces transient storage, exposes beacon chain roots,
introduces a new blob-carrying transaction type, adds a memory copying
instruction, limits self-destruct to only work for contracts created in the
same transaction, and adds an instruction to read the blob base fee.
".

Require ethereum.fork_criteria.
Axiom ethereum_fork_criteria_ByTimestamp :
  IsGlobalAlias globals ethereum.fork_criteria.globals "ByTimestamp".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "ByTimestamp" |),
    make_list [
      Constant.int 1710338135
    ],
    make_dict []
  |)
)).
