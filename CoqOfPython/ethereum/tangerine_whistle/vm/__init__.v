Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require typing.
Axiom typing_List :
  IsGlobalAlias globals typing.globals "List".
Axiom typing_Optional :
  IsGlobalAlias globals typing.globals "Optional".
Axiom typing_Set_ :
  IsGlobalAlias globals typing.globals "Set_".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".
Axiom ethereum_base_types_Bytes0 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes0".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_Hash32 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "Hash32".

Require ethereum.tangerine_whistle.blocks.
Axiom ethereum_tangerine_whistle_blocks_Log :
  IsGlobalAlias globals ethereum.tangerine_whistle.blocks.globals "Log".

Require ethereum.tangerine_whistle.fork_types.
Axiom ethereum_tangerine_whistle_fork_types_Address :
  IsGlobalAlias globals ethereum.tangerine_whistle.fork_types.globals "Address".

Require ethereum.tangerine_whistle.state.
Axiom ethereum_tangerine_whistle_state_State :
  IsGlobalAlias globals ethereum.tangerine_whistle.state.globals "State".

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
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
      M.get_field (| M.get_name (| globals, "child_evm" |), "gas_left" |)
    |) in
    M.pure Constant.None_)).
