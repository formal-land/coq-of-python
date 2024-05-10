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

Require ethereum.base_types.
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require ethereum.london.state.
Axiom ethereum_london_state_get_storage :
  IsGlobalAlias globals ethereum.london.state.globals "get_storage".
Axiom ethereum_london_state_get_storage_original :
  IsGlobalAlias globals ethereum.london.state.globals "get_storage_original".
Axiom ethereum_london_state_set_storage :
  IsGlobalAlias globals ethereum.london.state.globals "set_storage".

Require ethereum.london.vm.__init__.
Axiom ethereum_london_vm___init___Evm :
  IsGlobalAlias globals ethereum.london.vm.__init__.globals "Evm".

Require ethereum.london.vm.exceptions.
Axiom ethereum_london_vm_exceptions_OutOfGasError :
  IsGlobalAlias globals ethereum.london.vm.exceptions.globals "OutOfGasError".
Axiom ethereum_london_vm_exceptions_WriteInStaticContext :
  IsGlobalAlias globals ethereum.london.vm.exceptions.globals "WriteInStaticContext".

Require ethereum.london.vm.gas.
Axiom ethereum_london_vm_gas_GAS_CALL_STIPEND :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_CALL_STIPEND".
Axiom ethereum_london_vm_gas_GAS_COLD_SLOAD :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_COLD_SLOAD".
Axiom ethereum_london_vm_gas_GAS_STORAGE_CLEAR_REFUND :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_STORAGE_CLEAR_REFUND".
Axiom ethereum_london_vm_gas_GAS_STORAGE_SET :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_STORAGE_SET".
Axiom ethereum_london_vm_gas_GAS_STORAGE_UPDATE :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_STORAGE_UPDATE".
Axiom ethereum_london_vm_gas_GAS_WARM_ACCESS :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_WARM_ACCESS".
Axiom ethereum_london_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "charge_gas".

Require ethereum.london.vm.stack.
Axiom ethereum_london_vm_stack_pop :
  IsGlobalAlias globals ethereum.london.vm.stack.globals "pop".
Axiom ethereum_london_vm_stack_push :
  IsGlobalAlias globals ethereum.london.vm.stack.globals "push".

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
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.in (|
          make_tuple [ M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |); M.get_name (| globals, "key" |) ],
          M.get_field (| M.get_name (| globals, "evm" |), "accessed_storage_keys" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_WARM_ACCESS" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "accessed_storage_keys" |), "add" |),
    make_list [
      make_tuple [ M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |); M.get_name (| globals, "key" |) ]
    ],
    make_dict []
  |) in
        let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_COLD_SLOAD" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
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
    let gas_cost :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_in (|
          make_tuple [ M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |); M.get_name (| globals, "key" |) ],
          M.get_field (| M.get_name (| globals, "evm" |), "accessed_storage_keys" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "accessed_storage_keys" |), "add" |),
    make_list [
      make_tuple [ M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |); M.get_name (| globals, "key" |) ]
    ],
    make_dict []
  |) in
        let gas_cost := BinOp.add
          M.get_name (| globals, "GAS_COLD_SLOAD" |)
          M.get_name (| globals, "GAS_COLD_SLOAD" |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.eq (|
            M.get_name (| globals, "original_value" |),
            M.get_name (| globals, "current_value" |)
          |),
          ltac:(M.monadic (
            Compare.not_eq (|
              M.get_name (| globals, "current_value" |),
              M.get_name (| globals, "new_value" |)
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_name (| globals, "original_value" |),
              Constant.int 0
            |),
          (* then *)
          ltac:(M.monadic (
            let gas_cost := BinOp.add
              M.get_name (| globals, "GAS_STORAGE_SET" |)
              M.get_name (| globals, "GAS_STORAGE_SET" |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let gas_cost := BinOp.add
              BinOp.sub (|
    M.get_name (| globals, "GAS_STORAGE_UPDATE" |),
    M.get_name (| globals, "GAS_COLD_SLOAD" |)
  |)
              BinOp.sub (|
    M.get_name (| globals, "GAS_STORAGE_UPDATE" |),
    M.get_name (| globals, "GAS_COLD_SLOAD" |)
  |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let gas_cost := BinOp.add
          M.get_name (| globals, "GAS_WARM_ACCESS" |)
          M.get_name (| globals, "GAS_WARM_ACCESS" |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_name (| globals, "current_value" |),
          M.get_name (| globals, "new_value" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              Compare.not_eq (|
                M.get_name (| globals, "original_value" |),
                Constant.int 0
              |),
              ltac:(M.monadic (
                BoolOp.and (|
                  Compare.not_eq (|
                    M.get_name (| globals, "current_value" |),
                    Constant.int 0
                  |),
                  ltac:(M.monadic (
                    Compare.eq (|
                      M.get_name (| globals, "new_value" |),
                      Constant.int 0
                    |)
                  ))
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_op (|
              BinOp.add,
              M.get_field (| M.get_name (| globals, "evm" |), "refund_counter" |),
              M.call (|
    M.get_name (| globals, "int" |),
    make_list [
      M.get_name (| globals, "GAS_STORAGE_CLEAR_REFUND" |)
    ],
    make_dict []
  |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              Compare.not_eq (|
                M.get_name (| globals, "original_value" |),
                Constant.int 0
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_name (| globals, "current_value" |),
                  Constant.int 0
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_op (|
              BinOp.sub,
              M.get_field (| M.get_name (| globals, "evm" |), "refund_counter" |),
              M.call (|
    M.get_name (| globals, "int" |),
    make_list [
      M.get_name (| globals, "GAS_STORAGE_CLEAR_REFUND" |)
    ],
    make_dict []
  |)
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
              M.get_name (| globals, "original_value" |),
              M.get_name (| globals, "new_value" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.eq (|
                  M.get_name (| globals, "original_value" |),
                  Constant.int 0
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.assign_op (|
                  BinOp.add,
                  M.get_field (| M.get_name (| globals, "evm" |), "refund_counter" |),
                  M.call (|
    M.get_name (| globals, "int" |),
    make_list [
      BinOp.sub (|
        M.get_name (| globals, "GAS_STORAGE_SET" |),
        M.get_name (| globals, "GAS_WARM_ACCESS" |)
      |)
    ],
    make_dict []
  |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ := M.assign_op (|
                  BinOp.add,
                  M.get_field (| M.get_name (| globals, "evm" |), "refund_counter" |),
                  M.call (|
    M.get_name (| globals, "int" |),
    make_list [
      BinOp.sub (|
        BinOp.sub (|
          M.get_name (| globals, "GAS_STORAGE_UPDATE" |),
          M.get_name (| globals, "GAS_COLD_SLOAD" |)
        |),
        M.get_name (| globals, "GAS_WARM_ACCESS" |)
      |)
    ],
    make_dict []
  |)
                |) in
                M.pure Constant.None_
              )) |) in
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
