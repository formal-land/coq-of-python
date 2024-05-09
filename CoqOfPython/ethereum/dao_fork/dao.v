Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require state.
Axiom state_State :
  IsGlobalAlias globals state.globals "State".
Axiom state_get_account :
  IsGlobalAlias globals state.globals "get_account".
Axiom state_move_ether :
  IsGlobalAlias globals state.globals "move_ether".

Require utils.hexadecimal.
Axiom utils_hexadecimal_hex_to_address :
  IsGlobalAlias globals utils.hexadecimal.globals "hex_to_address".

Definition DAO_ACCOUNTS : Value.t := M.run ltac:(M.monadic (
  [M.call (|
    M.get_name (| globals, "hex_to_address" |),
    make_list [
      M.get_name (| globals, "address" |)
    ],
    make_dict []
  |) for (* At expr: unsupported node type: list *)]
)).

Definition DAO_RECOVERY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "hex_to_address" |),
    make_list [
      Constant.str "0xbf4ed7b27f1d666546e30d74d50d173d20bca754"
    ],
    make_dict []
  |)
)).

Definition apply_dao : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state" ] |) in
    let _ := Constant.str "
    Apply the dao fork to the state.

    Parameters
    ----------
    state :
        State before applying the DAO Fork.
    " in
    For M.get_name (| globals, "address" |) in M.get_name (| globals, "DAO_ACCOUNTS" |) do
      let balance :=
        M.get_field (| M.call (|
          M.get_name (| globals, "get_account" |),
          make_list [
            M.get_name (| globals, "state" |);
            M.get_name (| globals, "address" |)
          ],
          make_dict []
        |), "balance" |) in
      let _ := M.call (|
    M.get_name (| globals, "move_ether" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "address" |);
      M.get_name (| globals, "DAO_RECOVERY" |);
      M.get_name (| globals, "balance" |)
    ],
    make_dict []
  |) in
    EndFor.
    M.pure Constant.None_)).
