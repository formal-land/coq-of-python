Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.dao_fork.dao".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Dao Fork
^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

The Dao Fork was an irregular state change that moved all Ether from a large
collection of accounts (The Dao and all its children) to a recovery contract.

The recovery contract was previously created using normal contract deployment.
".

Axiom ethereum_dao_fork_state_imports_State :
  IsImported globals "ethereum.dao_fork.state" "State".
Axiom ethereum_dao_fork_state_imports_get_account :
  IsImported globals "ethereum.dao_fork.state" "get_account".
Axiom ethereum_dao_fork_state_imports_move_ether :
  IsImported globals "ethereum.dao_fork.state" "move_ether".

Axiom ethereum_dao_fork_utils_hexadecimal_imports_hex_to_address :
  IsImported globals "ethereum.dao_fork.utils.hexadecimal" "hex_to_address".

Definition DAO_ACCOUNTS : Value.t := M.run ltac:(M.monadic (
  Constant.str "(* At expr: unsupported node type: ListComp *)"
)).

Definition DAO_RECOVERY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "hex_to_address" |),
    make_list [
      Constant.str "0xbf4ed7b27f1d666546e30d74d50d173d20bca754"
    ],
    make_dict []
  |)
)).

Definition apply_dao : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Apply the dao fork to the state.

    Parameters
    ----------
    state :
        State before applying the DAO Fork.
    " in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "address" |),
        M.get_name (| globals, locals_stack, "DAO_ACCOUNTS" |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "balance" ,
            M.get_field (| M.call (|
              M.get_name (| globals, locals_stack, "get_account" |),
              make_list [
                M.get_name (| globals, locals_stack, "state" |);
                M.get_name (| globals, locals_stack, "address" |)
              ],
              make_dict []
            |), "balance" |)
          |) in
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "move_ether" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.get_name (| globals, locals_stack, "DAO_RECOVERY" |);
      M.get_name (| globals, locals_stack, "balance" |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    M.pure Constant.None_)).

Axiom apply_dao_in_globals :
  IsInGlobals globals "apply_dao" (make_function apply_dao).
