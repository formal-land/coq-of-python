Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.london.vm.__init__".

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

The abstract computer which runs the code stored in an
`.fork_types.Account`.
".

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_List :
  IsImported globals "typing" "List".
Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Set :
  IsImported globals "typing" "Set".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Axiom ethereum_base_types_imports_U64 :
  IsImported globals "ethereum.base_types" "U64".
Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".
Axiom ethereum_base_types_imports_Bytes32 :
  IsImported globals "ethereum.base_types" "Bytes32".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_crypto_hash_imports_Hash32 :
  IsImported globals "ethereum.crypto.hash" "Hash32".

Axiom ethereum_london_blocks_imports_Log :
  IsImported globals "ethereum.london.blocks" "Log".

Axiom ethereum_london_fork_types_imports_Address :
  IsImported globals "ethereum.london.fork_types" "Address".

Axiom ethereum_london_state_imports_State :
  IsImported globals "ethereum.london.state" "State".
Axiom ethereum_london_state_imports_account_exists_and_is_empty :
  IsImported globals "ethereum.london.state" "account_exists_and_is_empty".

Axiom ethereum_london_vm_precompiled_contracts_imports_RIPEMD160_ADDRESS :
  IsImported globals "ethereum.london.vm.precompiled_contracts" "RIPEMD160_ADDRESS".

Definition __all__ : Value.t := M.run ltac:(M.monadic (
  make_tuple [ Constant.str "Environment"; Constant.str "Evm"; Constant.str "Message" ]
)).

Definition Environment : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition Message : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition Evm : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition incorporate_child_on_success : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "child_evm" ] |) in
    let _ := Constant.str "
    Incorporate the state of a successful `child_evm` into the parent `evm`.

    Parameters
    ----------
    evm :
        The parent `EVM`.
    child_evm :
        The child evm to incorporate.
    " in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
      M.get_field (| M.get_name (| globals, "child_evm" |), "gas_left" |)
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "logs" |),
      M.get_field (| M.get_name (| globals, "child_evm" |), "logs" |)
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "refund_counter" |),
      M.get_field (| M.get_name (| globals, "child_evm" |), "refund_counter" |)
    |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "accounts_to_delete" |), "update" |),
    make_list [
      M.get_field (| M.get_name (| globals, "child_evm" |), "accounts_to_delete" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "touched_accounts" |), "update" |),
    make_list [
      M.get_field (| M.get_name (| globals, "child_evm" |), "touched_accounts" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "account_exists_and_is_empty" |),
          make_list [
            M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
            M.get_field (| M.get_field (| M.get_name (| globals, "child_evm" |), "message" |), "current_target" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "touched_accounts" |), "add" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, "child_evm" |), "message" |), "current_target" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "accessed_addresses" |), "update" |),
    make_list [
      M.get_field (| M.get_name (| globals, "child_evm" |), "accessed_addresses" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "accessed_storage_keys" |), "update" |),
    make_list [
      M.get_field (| M.get_name (| globals, "child_evm" |), "accessed_storage_keys" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition incorporate_child_on_error : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "child_evm" ] |) in
    let _ := Constant.str "
    Incorporate the state of an unsuccessful `child_evm` into the parent `evm`.

    Parameters
    ----------
    evm :
        The parent `EVM`.
    child_evm :
        The child evm to incorporate.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.in_ (|
          M.get_name (| globals, "RIPEMD160_ADDRESS" |),
          M.get_field (| M.get_name (| globals, "child_evm" |), "touched_accounts" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "touched_accounts" |), "add" |),
    make_list [
      M.get_name (| globals, "RIPEMD160_ADDRESS" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_field (| M.get_field (| M.get_name (| globals, "child_evm" |), "message" |), "current_target" |),
          M.get_name (| globals, "RIPEMD160_ADDRESS" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, "account_exists_and_is_empty" |),
              make_list [
                M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
                M.get_field (| M.get_field (| M.get_name (| globals, "child_evm" |), "message" |), "current_target" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "touched_accounts" |), "add" |),
    make_list [
      M.get_name (| globals, "RIPEMD160_ADDRESS" |)
    ],
    make_dict []
  |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
      M.get_field (| M.get_name (| globals, "child_evm" |), "gas_left" |)
    |) in
    M.pure Constant.None_)).
