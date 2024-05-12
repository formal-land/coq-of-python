Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.istanbul.__init__".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
The Istanbul fork makes changes to the gas costs of EVM instructions and data,
adds a cryptographic primitive, and introduces an instruction to fetch the
current chain identifier.
".

Axiom ethereum_fork_criteria_imports_ByBlockNumber :
  IsImported globals "ethereum.fork_criteria" "ByBlockNumber".

Definition FORK_CRITERIA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "ByBlockNumber" |),
    make_list [
      Constant.int 9069000
    ],
    make_dict []
  |)
)).
