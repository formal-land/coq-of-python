Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Storage Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM storage related instructions.
".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require state.
Axiom state_get_storage :
  IsGlobalAlias globals state.globals "get_storage".
Axiom state_get_storage_original :
  IsGlobalAlias globals state.globals "get_storage_original".
Axiom state_set_storage :
  IsGlobalAlias globals state.globals "set_storage".

Require __init__.
Axiom __init___Evm :
  IsGlobalAlias globals __init__.globals "Evm".

Require exceptions.
Axiom exceptions_OutOfGasError :
  IsGlobalAlias globals exceptions.globals "OutOfGasError".
Axiom exceptions_WriteInStaticContext :
  IsGlobalAlias globals exceptions.globals "WriteInStaticContext".

Require gas.
Axiom gas_GAS_CALL_STIPEND :
  IsGlobalAlias globals gas.globals "GAS_CALL_STIPEND".
Axiom gas_GAS_SLOAD :
  IsGlobalAlias globals gas.globals "GAS_SLOAD".
Axiom gas_GAS_STORAGE_CLEAR_REFUND :
  IsGlobalAlias globals gas.globals "GAS_STORAGE_CLEAR_REFUND".
Axiom gas_GAS_STORAGE_SET :
  IsGlobalAlias globals gas.globals "GAS_STORAGE_SET".
Axiom gas_GAS_STORAGE_UPDATE :
  IsGlobalAlias globals gas.globals "GAS_STORAGE_UPDATE".
Axiom gas_charge_gas :
  IsGlobalAlias globals gas.globals "charge_gas".

Require stack.
Axiom stack_pop :
  IsGlobalAlias globals stack.globals "pop".
Axiom stack_push :
  IsGlobalAlias globals stack.globals "push".

Definition sload : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Loads to the stack, the value corresponding to a certain key from the
    storage of the current account.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let key :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_SLOAD" |)
    ],
    make_dict []
  |) in
    let value :=
      M.call (|
        M.get_name (| globals, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition sstore : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Stores a value at a certain key in the current context's storage.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let key :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |) in
    let new_value :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt (|
        M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
        M.get_name (| globals, "GAS_CALL_STIPEND" |)
      |);
      M.get_name (| globals, "OutOfGasError" |)
    ],
    make_dict []
  |) in
    let original_value :=
      M.call (|
        M.get_name (| globals, "get_storage_original" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |) in
    let current_value :=
      M.call (|
        M.get_name (| globals, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |) in
    let _ :=
        let gas_cost :=
          M.get_name (| globals, "GAS_SLOAD" |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "gas_cost" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      UnOp.not (| M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "is_static" |) |);
      M.get_name (| globals, "WriteInStaticContext" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "set_storage" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, "key" |);
      M.get_name (| globals, "new_value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).
