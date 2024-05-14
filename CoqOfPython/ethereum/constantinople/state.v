Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.constantinople.state".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
State
^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

The state contains all information that is preserved between transactions.

It consists of a main account trie and storage tries for each contract.

There is a distinction between an account that does not exist and
`EMPTY_ACCOUNT`.
".

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".
Axiom dataclasses_imports_field :
  IsImported globals "dataclasses" "field".

Axiom typing_imports_Callable :
  IsImported globals "typing" "Callable".
Axiom typing_imports_Dict :
  IsImported globals "typing" "Dict".
Axiom typing_imports_List :
  IsImported globals "typing" "List".
Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".
Axiom ethereum_base_types_imports_modify :
  IsImported globals "ethereum.base_types" "modify".

Axiom ethereum_utils_ensure_imports_ensure :
  IsImported globals "ethereum.utils.ensure" "ensure".

Axiom ethereum_constantinople_fork_types_imports_EMPTY_ACCOUNT :
  IsImported globals "ethereum.constantinople.fork_types" "EMPTY_ACCOUNT".
Axiom ethereum_constantinople_fork_types_imports_Account :
  IsImported globals "ethereum.constantinople.fork_types" "Account".
Axiom ethereum_constantinople_fork_types_imports_Address :
  IsImported globals "ethereum.constantinople.fork_types" "Address".
Axiom ethereum_constantinople_fork_types_imports_Root :
  IsImported globals "ethereum.constantinople.fork_types" "Root".

Axiom ethereum_constantinople_trie_imports_EMPTY_TRIE_ROOT :
  IsImported globals "ethereum.constantinople.trie" "EMPTY_TRIE_ROOT".
Axiom ethereum_constantinople_trie_imports_Trie :
  IsImported globals "ethereum.constantinople.trie" "Trie".
Axiom ethereum_constantinople_trie_imports_copy_trie :
  IsImported globals "ethereum.constantinople.trie" "copy_trie".
Axiom ethereum_constantinople_trie_imports_root :
  IsImported globals "ethereum.constantinople.trie" "root".
Axiom ethereum_constantinople_trie_imports_trie_get :
  IsImported globals "ethereum.constantinople.trie" "trie_get".
Axiom ethereum_constantinople_trie_imports_trie_set :
  IsImported globals "ethereum.constantinople.trie" "trie_set".

Definition State : Value.t := builtins.make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition close_state : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Free resources held by the state. Used by optimized implementations to
    release file descriptors.
    " in
    let _ := M.delete (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_main_trie" |) |) in
    let _ := M.delete (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |) |) in
    let _ := M.delete (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_snapshots" |) |) in
    M.pure Constant.None_)).

Axiom close_state_in_globals :
  IsInGlobals globals "close_state" (make_function close_state).

Definition begin_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Start a state transaction.

    Transactions are entirely implicit and can be nested. It is not possible to
    calculate the state root during a transaction.

    Parameters
    ----------
    state : State
        The state.
    " in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_snapshots" |), "append" |),
    make_list [
      make_tuple [ M.call (|
        M.get_name (| globals, locals_stack, "copy_trie" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_main_trie" |)
        ],
        make_dict []
      |); Constant.str "(* At expr: unsupported node type: DictComp *)" ]
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom begin_transaction_in_globals :
  IsInGlobals globals "begin_transaction" (make_function begin_transaction).

Definition commit_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Commit a state transaction.

    Parameters
    ----------
    state : State
        The state.
    " in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_snapshots" |), "pop" |),
    make_list [],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom commit_transaction_in_globals :
  IsInGlobals globals "commit_transaction" (make_function commit_transaction).

Definition rollback_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Rollback a state transaction, resetting the state to the point when the
    corresponding `start_transaction()` call was made.

    Parameters
    ----------
    state : State
        The state.
    " in
    let _ := M.assign (|
      make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_main_trie" |); M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |) ],
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_snapshots" |), "pop" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom rollback_transaction_in_globals :
  IsInGlobals globals "rollback_transaction" (make_function rollback_transaction).

Definition get_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Get the `Account` object at an address. Returns `EMPTY_ACCOUNT` if there
    is no account at the address.

    Use `get_account_optional()` if you care about the difference between a
    non-existent account and `EMPTY_ACCOUNT`.

    Parameters
    ----------
    state: `State`
        The state
    address : `Address`
        Address to lookup.

    Returns
    -------
    account : `Account`
        Account at address.
    " in
    let _ := M.assign_local (|
      "account" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_account_optional" |),
        make_list [
          M.get_name (| globals, locals_stack, "state" |);
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "account" |);
            M.get_name (| globals, locals_stack, "Account" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "account" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "EMPTY_ACCOUNT" |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom get_account_in_globals :
  IsInGlobals globals "get_account" (make_function get_account).

Definition get_account_optional : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Get the `Account` object at an address. Returns `None` (rather than
    `EMPTY_ACCOUNT`) if there is no account at the address.

    Parameters
    ----------
    state: `State`
        The state
    address : `Address`
        Address to lookup.

    Returns
    -------
    account : `Account`
        Account at address.
    " in
    let _ := M.assign_local (|
      "account" ,
      M.call (|
        M.get_name (| globals, locals_stack, "trie_get" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_main_trie" |);
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "account" |)
    |) in
    M.pure Constant.None_)).

Axiom get_account_optional_in_globals :
  IsInGlobals globals "get_account_optional" (make_function get_account_optional).

Definition set_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address"; "account" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Set the `Account` object at an address. Setting to `None` deletes
    the account (but not its storage, see `destroy_account()`).

    Parameters
    ----------
    state: `State`
        The state
    address : `Address`
        Address to set.
    account : `Account`
        Account to set at address.
    " in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "trie_set" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_main_trie" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.get_name (| globals, locals_stack, "account" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom set_account_in_globals :
  IsInGlobals globals "set_account" (make_function set_account).

Definition destroy_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Completely remove the account at `address` and all of its storage.

    This function is made available exclusively for the `SELFDESTRUCT`
    opcode. It is expected that `SELFDESTRUCT` will be disabled in a future
    hardfork and this function will be removed.

    Parameters
    ----------
    state: `State`
        The state
    address : `Address`
        Address of account to destroy.
    " in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "destroy_storage" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_account" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      Constant.None_
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom destroy_account_in_globals :
  IsInGlobals globals "destroy_account" (make_function destroy_account).

Definition destroy_storage : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Completely remove the storage at `address`.

    Parameters
    ----------
    state: `State`
        The state
    address : `Address`
        Address of account whose storage is to be deleted.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.in_ (|
          M.get_name (| globals, locals_stack, "address" |),
          M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.delete (| M.get_subscript (|
    M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |),
    M.get_name (| globals, locals_stack, "address" |)
  |) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom destroy_storage_in_globals :
  IsInGlobals globals "destroy_storage" (make_function destroy_storage).

Definition get_storage : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address"; "key" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Get a value at a storage key on an account. Returns `U256(0)` if the
    storage key has not been set previously.

    Parameters
    ----------
    state: `State`
        The state
    address : `Address`
        Address of the account.
    key : `Bytes`
        Key to lookup.

    Returns
    -------
    value : `U256`
        Value at the key.
    " in
    let _ := M.assign_local (|
      "trie" ,
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |), "get" |),
        make_list [
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.is (|
          M.get_name (| globals, locals_stack, "trie" |),
          Constant.None_
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "trie_get" |),
        make_list [
          M.get_name (| globals, locals_stack, "trie" |);
          M.get_name (| globals, locals_stack, "key" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assert (| M.call (|
    M.get_name (| globals, locals_stack, "isinstance" |),
    make_list [
      M.get_name (| globals, locals_stack, "value" |);
      M.get_name (| globals, locals_stack, "U256" |)
    ],
    make_dict []
  |) |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "value" |)
    |) in
    M.pure Constant.None_)).

Axiom get_storage_in_globals :
  IsInGlobals globals "get_storage" (make_function get_storage).

Definition set_storage : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address"; "key"; "value" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Set a value at a storage key on an account. Setting to `U256(0)` deletes
    the key.

    Parameters
    ----------
    state: `State`
        The state
    address : `Address`
        Address of the account.
    key : `Bytes`
        Key to set.
    value : `U256`
        Value to set at the key.
    " in
    let _ := M.assert (| Compare.is_not (|
    M.call (|
      M.get_name (| globals, locals_stack, "trie_get" |),
      make_list [
        M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_main_trie" |);
        M.get_name (| globals, locals_stack, "address" |)
      ],
      make_dict []
    |),
    Constant.None_
  |) |) in
    let _ := M.assign_local (|
      "trie" ,
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |), "get" |),
        make_list [
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.is (|
          M.get_name (| globals, locals_stack, "trie" |),
          Constant.None_
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "trie" ,
          M.call (|
            M.get_name (| globals, locals_stack, "Trie" |),
            make_list [],
            make_dict []
          |)
        |) in
        let _ := M.assign (|
          M.get_subscript (|
            M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |),
            M.get_name (| globals, locals_stack, "address" |)
          |),
          M.get_name (| globals, locals_stack, "trie" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "trie_set" |),
    make_list [
      M.get_name (| globals, locals_stack, "trie" |);
      M.get_name (| globals, locals_stack, "key" |);
      M.get_name (| globals, locals_stack, "value" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "_data" |),
          Constant.str "(* At expr: unsupported node type: Dict *)"
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.delete (| M.get_subscript (|
    M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |),
    M.get_name (| globals, locals_stack, "address" |)
  |) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom set_storage_in_globals :
  IsInGlobals globals "set_storage" (make_function set_storage).

Definition storage_root : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Calculate the storage root of an account.

    Parameters
    ----------
    state:
        The state
    address :
        Address of the account.

    Returns
    -------
    root : `Root`
        Storage root of the account.
    " in
    let _ := M.assert (| UnOp.not (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_snapshots" |) |) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.in_ (|
          M.get_name (| globals, locals_stack, "address" |),
          M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "root" |),
            make_list [
              M.get_subscript (|
                M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_storage_tries" |),
                M.get_name (| globals, locals_stack, "address" |)
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "EMPTY_TRIE_ROOT" |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom storage_root_in_globals :
  IsInGlobals globals "storage_root" (make_function storage_root).

Definition state_root : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Calculate the state root.

    Parameters
    ----------
    state:
        The current state.

    Returns
    -------
    root : `Root`
        The state root.
    " in
    let _ := M.assert (| UnOp.not (| M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_snapshots" |) |) |) in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "root" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "state" |), "_main_trie" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom state_root_in_globals :
  IsInGlobals globals "state_root" (make_function state_root).

Definition account_exists : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Checks if an account exists in the state trie

    Parameters
    ----------
    state:
        The state
    address:
        Address of the account that needs to be checked.

    Returns
    -------
    account_exists : `bool`
        True if account exists in the state trie, False otherwise
    " in
    let _ := M.return_ (|
      Compare.is_not (|
        M.call (|
          M.get_name (| globals, locals_stack, "get_account_optional" |),
          make_list [
            M.get_name (| globals, locals_stack, "state" |);
            M.get_name (| globals, locals_stack, "address" |)
          ],
          make_dict []
        |),
        Constant.None_
      |)
    |) in
    M.pure Constant.None_)).

Axiom account_exists_in_globals :
  IsInGlobals globals "account_exists" (make_function account_exists).

Definition account_has_code_or_nonce : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Checks if an account has non zero nonce or non empty code

    Parameters
    ----------
    state:
        The state
    address:
        Address of the account that needs to be checked.

    Returns
    -------
    has_code_or_nonce : `bool`
        True if if an account has non zero nonce or non empty code,
        False otherwise.
    " in
    let _ := M.assign_local (|
      "account" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_name (| globals, locals_stack, "state" |);
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      BoolOp.or (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "account" |), "nonce" |),
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |),
        ltac:(M.monadic (
          Compare.not_eq (|
            M.get_field (| M.get_name (| globals, locals_stack, "account" |), "code" |),
            Constant.bytes ""
          |)
        ))
      |)
    |) in
    M.pure Constant.None_)).

Axiom account_has_code_or_nonce_in_globals :
  IsInGlobals globals "account_has_code_or_nonce" (make_function account_has_code_or_nonce).

Definition is_account_empty : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Checks if an account has zero nonce, empty code and zero balance.

    Parameters
    ----------
    state:
        The state
    address:
        Address of the account that needs to be checked.

    Returns
    -------
    is_empty : `bool`
        True if if an account has zero nonce, empty code and zero balance,
        False otherwise.
    " in
    let _ := M.assign_local (|
      "account" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_name (| globals, locals_stack, "state" |);
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      BoolOp.and (|
        Compare.eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "account" |), "nonce" |),
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |),
        ltac:(M.monadic (
          BoolOp.and (|
            Compare.eq (|
              M.get_field (| M.get_name (| globals, locals_stack, "account" |), "code" |),
              Constant.bytes ""
            |),
            ltac:(M.monadic (
              Compare.eq (|
                M.get_field (| M.get_name (| globals, locals_stack, "account" |), "balance" |),
                Constant.int 0
              |)
            ))
          |)
        ))
      |)
    |) in
    M.pure Constant.None_)).

Axiom is_account_empty_in_globals :
  IsInGlobals globals "is_account_empty" (make_function is_account_empty).

Definition account_exists_and_is_empty : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Checks if an account exists and has zero nonce, empty code and zero
    balance.

    Parameters
    ----------
    state:
        The state
    address:
        Address of the account that needs to be checked.

    Returns
    -------
    exists_and_is_empty : `bool`
        True if an account exists and has zero nonce, empty code and zero
        balance, False otherwise.
    " in
    let _ := M.assign_local (|
      "account" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_account_optional" |),
        make_list [
          M.get_name (| globals, locals_stack, "state" |);
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      BoolOp.and (|
        Compare.is_not (|
          M.get_name (| globals, locals_stack, "account" |),
          Constant.None_
        |),
        ltac:(M.monadic (
          BoolOp.and (|
            Compare.eq (|
              M.get_field (| M.get_name (| globals, locals_stack, "account" |), "nonce" |),
              M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |)
            |),
            ltac:(M.monadic (
              BoolOp.and (|
                Compare.eq (|
                  M.get_field (| M.get_name (| globals, locals_stack, "account" |), "code" |),
                  Constant.bytes ""
                |),
                ltac:(M.monadic (
                  Compare.eq (|
                    M.get_field (| M.get_name (| globals, locals_stack, "account" |), "balance" |),
                    Constant.int 0
                  |)
                ))
              |)
            ))
          |)
        ))
      |)
    |) in
    M.pure Constant.None_)).

Axiom account_exists_and_is_empty_in_globals :
  IsInGlobals globals "account_exists_and_is_empty" (make_function account_exists_and_is_empty).

Definition is_account_alive : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Check whether is an account is both in the state and non empty.

    Parameters
    ----------
    state:
        The state
    address:
        Address of the account that needs to be checked.

    Returns
    -------
    is_alive : `bool`
        True if the account is alive.
    " in
    let _ := M.assign_local (|
      "account" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_account_optional" |),
        make_list [
          M.get_name (| globals, locals_stack, "state" |);
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.is (|
          M.get_name (| globals, locals_stack, "account" |),
          Constant.None_
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.bool false
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          UnOp.not (| BoolOp.and (|
            Compare.eq (|
              M.get_field (| M.get_name (| globals, locals_stack, "account" |), "nonce" |),
              M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |)
            |),
            ltac:(M.monadic (
              BoolOp.and (|
                Compare.eq (|
                  M.get_field (| M.get_name (| globals, locals_stack, "account" |), "code" |),
                  Constant.bytes ""
                |),
                ltac:(M.monadic (
                  Compare.eq (|
                    M.get_field (| M.get_name (| globals, locals_stack, "account" |), "balance" |),
                    Constant.int 0
                  |)
                ))
              |)
            ))
          |) |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom is_account_alive_in_globals :
  IsInGlobals globals "is_account_alive" (make_function is_account_alive).

Definition modify_state : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address"; "f" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Modify an `Account` in the `State`.
    " in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_account" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.call (|
        M.get_name (| globals, locals_stack, "modify" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "get_account" |),
            make_list [
              M.get_name (| globals, locals_stack, "state" |);
              M.get_name (| globals, locals_stack, "address" |)
            ],
            make_dict []
          |);
          M.get_name (| globals, locals_stack, "f" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom modify_state_in_globals :
  IsInGlobals globals "modify_state" (make_function modify_state).

Definition move_ether : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "sender_address"; "recipient_address"; "amount" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Move funds between accounts.
    " in
(* At stmt: unsupported node type: FunctionDef *)
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "modify_state" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "sender_address" |);
      M.get_name (| globals, locals_stack, "reduce_sender_balance" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "modify_state" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "recipient_address" |);
      M.get_name (| globals, locals_stack, "increase_recipient_balance" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom move_ether_in_globals :
  IsInGlobals globals "move_ether" (make_function move_ether).

Definition set_account_balance : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address"; "amount" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Sets the balance of an account.

    Parameters
    ----------
    state:
        The current state.

    address:
        Address of the account whose nonce needs to be incremented.

    amount:
        The amount that needs to set in balance.
    " in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "modify_state" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.get_name (| globals, locals_stack, "set_balance" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom set_account_balance_in_globals :
  IsInGlobals globals "set_account_balance" (make_function set_account_balance).

Definition touch_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Initializes an account to state.

    Parameters
    ----------
    state:
        The current state.

    address:
        The address of the account that need to initialised.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        UnOp.not (| M.call (|
          M.get_name (| globals, locals_stack, "account_exists" |),
          make_list [
            M.get_name (| globals, locals_stack, "state" |);
            M.get_name (| globals, locals_stack, "address" |)
          ],
          make_dict []
        |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_account" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.get_name (| globals, locals_stack, "EMPTY_ACCOUNT" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom touch_account_in_globals :
  IsInGlobals globals "touch_account" (make_function touch_account).

Definition increment_nonce : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Increments the nonce of an account.

    Parameters
    ----------
    state:
        The current state.

    address:
        Address of the account whose nonce needs to be incremented.
    " in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "modify_state" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.get_name (| globals, locals_stack, "increase_nonce" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom increment_nonce_in_globals :
  IsInGlobals globals "increment_nonce" (make_function increment_nonce).

Definition set_code : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address"; "code" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Sets Account code.

    Parameters
    ----------
    state:
        The current state.

    address:
        Address of the account whose code needs to be update.

    code:
        The bytecode that needs to be set.
    " in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "modify_state" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.get_name (| globals, locals_stack, "write_code" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom set_code_in_globals :
  IsInGlobals globals "set_code" (make_function set_code).

Definition create_ether : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "address"; "amount" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Add newly created ether to an account.

    Parameters
    ----------
    state:
        The current state.
    address:
        Address of the account to which ether is added.
    amount:
        The amount of ether to be added to the account of interest.
    " in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "modify_state" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.get_name (| globals, locals_stack, "increase_balance" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom create_ether_in_globals :
  IsInGlobals globals "create_ether" (make_function create_ether).
