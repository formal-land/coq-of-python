Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".
Axiom dataclasses_field :
  IsGlobalAlias globals dataclasses.globals "field".

Require typing.
Axiom typing_Callable :
  IsGlobalAlias globals typing.globals "Callable".
Axiom typing_Dict :
  IsGlobalAlias globals typing.globals "Dict".
Axiom typing_List :
  IsGlobalAlias globals typing.globals "List".
Axiom typing_Optional :
  IsGlobalAlias globals typing.globals "Optional".
Axiom typing_Set_ :
  IsGlobalAlias globals typing.globals "Set_".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".
Axiom ethereum_base_types_modify :
  IsGlobalAlias globals ethereum.base_types.globals "modify".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require ethereum.shanghai.blocks.
Axiom ethereum_shanghai_blocks_Withdrawal :
  IsGlobalAlias globals ethereum.shanghai.blocks.globals "Withdrawal".

Require ethereum.shanghai.fork_types.
Axiom ethereum_shanghai_fork_types_EMPTY_ACCOUNT :
  IsGlobalAlias globals ethereum.shanghai.fork_types.globals "EMPTY_ACCOUNT".
Axiom ethereum_shanghai_fork_types_Account :
  IsGlobalAlias globals ethereum.shanghai.fork_types.globals "Account".
Axiom ethereum_shanghai_fork_types_Address :
  IsGlobalAlias globals ethereum.shanghai.fork_types.globals "Address".
Axiom ethereum_shanghai_fork_types_Root :
  IsGlobalAlias globals ethereum.shanghai.fork_types.globals "Root".

Require ethereum.shanghai.trie.
Axiom ethereum_shanghai_trie_EMPTY_TRIE_ROOT :
  IsGlobalAlias globals ethereum.shanghai.trie.globals "EMPTY_TRIE_ROOT".
Axiom ethereum_shanghai_trie_Trie :
  IsGlobalAlias globals ethereum.shanghai.trie.globals "Trie".
Axiom ethereum_shanghai_trie_copy_trie :
  IsGlobalAlias globals ethereum.shanghai.trie.globals "copy_trie".
Axiom ethereum_shanghai_trie_root :
  IsGlobalAlias globals ethereum.shanghai.trie.globals "root".
Axiom ethereum_shanghai_trie_trie_get :
  IsGlobalAlias globals ethereum.shanghai.trie.globals "trie_get".
Axiom ethereum_shanghai_trie_trie_set :
  IsGlobalAlias globals ethereum.shanghai.trie.globals "trie_set".

Definition State : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition close_state : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state" ] |) in
    let _ := Constant.str "
    Free resources held by the state. Used by optimized implementations to
    release file descriptors.
    " in
    let _ := M.delete (| M.get_field (| M.get_name (| globals, "state" |), "_main_trie" |) |) in
    let _ := M.delete (| M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |) |) in
    let _ := M.delete (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |) |) in
    let _ := M.delete (| M.get_field (| M.get_name (| globals, "state" |), "_created_accounts" |) |) in
    M.pure Constant.None_)).

Definition begin_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state" ] |) in
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
    M.get_field (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |), "append" |),
    make_list [
      make_tuple [ M.call (|
        M.get_name (| globals, "copy_trie" |),
        make_list [
          M.get_field (| M.get_name (| globals, "state" |), "_main_trie" |)
        ],
        make_dict []
      |); Constant.str "(* At expr: unsupported node type: DictComp *)" ]
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition commit_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state" ] |) in
    let _ := Constant.str "
    Commit a state transaction.

    Parameters
    ----------
    state : State
        The state.
    " in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |), "pop" |),
    make_list [],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        UnOp.not (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "state" |), "_created_accounts" |), "clear" |),
    make_list [],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition rollback_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state" ] |) in
    let _ := Constant.str "
    Rollback a state transaction, resetting the state to the point when the
    corresponding `start_transaction()` call was made.

    Parameters
    ----------
    state : State
        The state.
    " in
    let _ := M.assign (|
      make_tuple [ M.get_field (| M.get_name (| globals, "state" |), "_main_trie" |); M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |) ],
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |), "pop" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        UnOp.not (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "state" |), "_created_accounts" |), "clear" |),
    make_list [],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition get_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    let account :=
      M.call (|
        M.get_name (| globals, "get_account_optional" |),
        make_list [
          M.get_name (| globals, "state" |);
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "isinstance" |),
          make_list [
            M.get_name (| globals, "account" |);
            M.get_name (| globals, "Account" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, "account" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, "EMPTY_ACCOUNT" |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition get_account_optional : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    let account :=
      M.call (|
        M.get_name (| globals, "trie_get" |),
        make_list [
          M.get_field (| M.get_name (| globals, "state" |), "_main_trie" |);
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.get_name (| globals, "account" |)
    |) in
    M.pure Constant.None_)).

Definition set_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address"; "account" ] |) in
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
    M.get_name (| globals, "trie_set" |),
    make_list [
      M.get_field (| M.get_name (| globals, "state" |), "_main_trie" |);
      M.get_name (| globals, "address" |);
      M.get_name (| globals, "account" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition destroy_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    M.get_name (| globals, "destroy_storage" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "address" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "set_account" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "address" |);
      Constant.None_
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition destroy_storage : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
        Compare.in (|
          M.get_name (| globals, "address" |),
          M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.delete (| M.get_subscript (| M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |), M.get_name (| globals, "address" |) |) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition mark_account_created : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
    let _ := Constant.str "
    Mark an account as having been created in the current transaction.
    This information is used by `get_storage_original()` to handle an obscure
    edgecase.

    The marker is not removed even if the account creation reverts. Since the
    account cannot have had code prior to its creation and can't call
    `get_storage_original()`, this is harmless.

    Parameters
    ----------
    state: `State`
        The state
    address : `Address`
        Address of the account that has been created.
    " in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "state" |), "_created_accounts" |), "add" |),
    make_list [
      M.get_name (| globals, "address" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition get_storage : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address"; "key" ] |) in
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
    let trie :=
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |), "get" |),
        make_list [
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.is (|
          M.get_name (| globals, "trie" |),
          Constant.None_
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "U256" |),
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
    let value :=
      M.call (|
        M.get_name (| globals, "trie_get" |),
        make_list [
          M.get_name (| globals, "trie" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |) in
    let _ := M.assert (| M.call (|
    M.get_name (| globals, "isinstance" |),
    make_list [
      M.get_name (| globals, "value" |);
      M.get_name (| globals, "U256" |)
    ],
    make_dict []
  |) |) in
    let _ := M.return_ (|
      M.get_name (| globals, "value" |)
    |) in
    M.pure Constant.None_)).

Definition set_storage : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address"; "key"; "value" ] |) in
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
      M.get_name (| globals, "trie_get" |),
      make_list [
        M.get_field (| M.get_name (| globals, "state" |), "_main_trie" |);
        M.get_name (| globals, "address" |)
      ],
      make_dict []
    |),
    Constant.None_
  |) |) in
    let trie :=
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |), "get" |),
        make_list [
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.is (|
          M.get_name (| globals, "trie" |),
          Constant.None_
        |),
      (* then *)
      ltac:(M.monadic (
        let trie :=
          M.call (|
            M.get_name (| globals, "Trie" |),
            make_list [],
            make_dict []
          |) in
        let _ := M.assign (|
          M.get_subscript (| M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |), M.get_name (| globals, "address" |) |),
          M.get_name (| globals, "trie" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "trie_set" |),
    make_list [
      M.get_name (| globals, "trie" |);
      M.get_name (| globals, "key" |);
      M.get_name (| globals, "value" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_field (| M.get_name (| globals, "trie" |), "_data" |),
          {}
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.delete (| M.get_subscript (| M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |), M.get_name (| globals, "address" |) |) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition storage_root : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    let _ := M.assert (| UnOp.not (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |) |) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.in (|
          M.get_name (| globals, "address" |),
          M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "root" |),
            make_list [
              M.get_subscript (| M.get_field (| M.get_name (| globals, "state" |), "_storage_tries" |), M.get_name (| globals, "address" |) |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, "EMPTY_TRIE_ROOT" |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition state_root : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state" ] |) in
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
    let _ := M.assert (| UnOp.not (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |) |) |) in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "root" |),
        make_list [
          M.get_field (| M.get_name (| globals, "state" |), "_main_trie" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition account_exists : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
          M.get_name (| globals, "get_account_optional" |),
          make_list [
            M.get_name (| globals, "state" |);
            M.get_name (| globals, "address" |)
          ],
          make_dict []
        |),
        Constant.None_
      |)
    |) in
    M.pure Constant.None_)).

Definition account_has_code_or_nonce : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    let account :=
      M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_name (| globals, "state" |);
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      BoolOp.or (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, "account" |), "nonce" |),
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |),
        ltac:(M.monadic (
          Compare.not_eq (|
            M.get_field (| M.get_name (| globals, "account" |), "code" |),
            Constant.bytes ""
          |)
        ))
      |)
    |) in
    M.pure Constant.None_)).

Definition is_account_empty : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    let account :=
      M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_name (| globals, "state" |);
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      BoolOp.and (|
        Compare.eq (|
          M.get_field (| M.get_name (| globals, "account" |), "nonce" |),
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |),
        ltac:(M.monadic (
          BoolOp.and (|
            Compare.eq (|
              M.get_field (| M.get_name (| globals, "account" |), "code" |),
              Constant.bytes ""
            |),
            ltac:(M.monadic (
              Compare.eq (|
                M.get_field (| M.get_name (| globals, "account" |), "balance" |),
                Constant.int 0
              |)
            ))
          |)
        ))
      |)
    |) in
    M.pure Constant.None_)).

Definition account_exists_and_is_empty : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    let account :=
      M.call (|
        M.get_name (| globals, "get_account_optional" |),
        make_list [
          M.get_name (| globals, "state" |);
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      BoolOp.and (|
        Compare.is_not (|
          M.get_name (| globals, "account" |),
          Constant.None_
        |),
        ltac:(M.monadic (
          BoolOp.and (|
            Compare.eq (|
              M.get_field (| M.get_name (| globals, "account" |), "nonce" |),
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |)
            |),
            ltac:(M.monadic (
              BoolOp.and (|
                Compare.eq (|
                  M.get_field (| M.get_name (| globals, "account" |), "code" |),
                  Constant.bytes ""
                |),
                ltac:(M.monadic (
                  Compare.eq (|
                    M.get_field (| M.get_name (| globals, "account" |), "balance" |),
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

Definition is_account_alive : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    let account :=
      M.call (|
        M.get_name (| globals, "get_account_optional" |),
        make_list [
          M.get_name (| globals, "state" |);
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.is (|
          M.get_name (| globals, "account" |),
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
              M.get_field (| M.get_name (| globals, "account" |), "nonce" |),
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |)
            |),
            ltac:(M.monadic (
              BoolOp.and (|
                Compare.eq (|
                  M.get_field (| M.get_name (| globals, "account" |), "code" |),
                  Constant.bytes ""
                |),
                ltac:(M.monadic (
                  Compare.eq (|
                    M.get_field (| M.get_name (| globals, "account" |), "balance" |),
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

Definition modify_state : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address"; "f" ] |) in
    let _ := Constant.str "
    Modify an `Account` in the `State`.
    " in
    let _ := M.call (|
    M.get_name (| globals, "set_account" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "address" |);
      M.call (|
        M.get_name (| globals, "modify" |),
        make_list [
          M.call (|
            M.get_name (| globals, "get_account" |),
            make_list [
              M.get_name (| globals, "state" |);
              M.get_name (| globals, "address" |)
            ],
            make_dict []
          |);
          M.get_name (| globals, "f" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition move_ether : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "sender_address"; "recipient_address"; "amount" ] |) in
    let _ := Constant.str "
    Move funds between accounts.
    " in
(* At stmt: unsupported node type: FunctionDef *)
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.call (|
    M.get_name (| globals, "modify_state" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "sender_address" |);
      M.get_name (| globals, "reduce_sender_balance" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "modify_state" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "recipient_address" |);
      M.get_name (| globals, "increase_recipient_balance" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition process_withdrawal : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "wd" ] |) in
    let _ := Constant.str "
    Increase the balance of the withdrawing account.
    " in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.call (|
    M.get_name (| globals, "modify_state" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_field (| M.get_name (| globals, "wd" |), "address" |);
      M.get_name (| globals, "increase_recipient_balance" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition set_account_balance : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address"; "amount" ] |) in
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
    M.get_name (| globals, "modify_state" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "address" |);
      M.get_name (| globals, "set_balance" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition touch_account : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
          M.get_name (| globals, "account_exists" |),
          make_list [
            M.get_name (| globals, "state" |);
            M.get_name (| globals, "address" |)
          ],
          make_dict []
        |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "set_account" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "address" |);
      M.get_name (| globals, "EMPTY_ACCOUNT" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition increment_nonce : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address" ] |) in
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
    M.get_name (| globals, "modify_state" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "address" |);
      M.get_name (| globals, "increase_nonce" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition set_code : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address"; "code" ] |) in
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
    M.get_name (| globals, "modify_state" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "address" |);
      M.get_name (| globals, "write_code" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition get_storage_original : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "address"; "key" ] |) in
    let _ := Constant.str "
    Get the original value in a storage slot i.e. the value before the current
    transaction began. This function reads the value from the snapshots taken
    before executing the transaction.

    Parameters
    ----------
    state:
        The current state.
    address:
        Address of the account to read the value from.
    key:
        Key of the storage slot.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.in (|
          M.get_name (| globals, "address" |),
          M.get_field (| M.get_name (| globals, "state" |), "_created_accounts" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "U256" |),
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
    let _ := M.assign (|
      make_tuple [ M.get_name (| globals, "_" |); M.get_name (| globals, "original_trie" |) ],
      M.get_subscript (| M.get_field (| M.get_name (| globals, "state" |), "_snapshots" |), Constant.int 0 |)
    |) in
    let original_account_trie :=
      M.call (|
        M.get_field (| M.get_name (| globals, "original_trie" |), "get" |),
        make_list [
          M.get_name (| globals, "address" |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.is (|
          M.get_name (| globals, "original_account_trie" |),
          Constant.None_
        |),
      (* then *)
      ltac:(M.monadic (
        let original_value :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let original_value :=
          M.call (|
            M.get_name (| globals, "trie_get" |),
            make_list [
              M.get_name (| globals, "original_account_trie" |);
              M.get_name (| globals, "key" |)
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assert (| M.call (|
    M.get_name (| globals, "isinstance" |),
    make_list [
      M.get_name (| globals, "original_value" |);
      M.get_name (| globals, "U256" |)
    ],
    make_dict []
  |) |) in
    let _ := M.return_ (|
      M.get_name (| globals, "original_value" |)
    |) in
    M.pure Constant.None_)).
