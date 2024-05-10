Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.istanbul.vm.instructions.storage".

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

Axiom ethereum_utils_ensure_imports_ensure :
  IsImported globals "ethereum.utils.ensure" "ensure".

Axiom ethereum_istanbul_state_imports_get_storage :
  IsImported globals "ethereum.istanbul.state" "get_storage".
Axiom ethereum_istanbul_state_imports_get_storage_original :
  IsImported globals "ethereum.istanbul.state" "get_storage_original".
Axiom ethereum_istanbul_state_imports_set_storage :
  IsImported globals "ethereum.istanbul.state" "set_storage".

Axiom ethereum_istanbul_vm_imports_Evm :
  IsImported globals "ethereum.istanbul.vm" "Evm".

Axiom ethereum_istanbul_vm_exceptions_imports_OutOfGasError :
  IsImported globals "ethereum.istanbul.vm.exceptions" "OutOfGasError".
Axiom ethereum_istanbul_vm_exceptions_imports_WriteInStaticContext :
  IsImported globals "ethereum.istanbul.vm.exceptions" "WriteInStaticContext".

Axiom ethereum_istanbul_vm_gas_imports_GAS_CALL_STIPEND :
  IsImported globals "ethereum.istanbul.vm.gas" "GAS_CALL_STIPEND".
Axiom ethereum_istanbul_vm_gas_imports_GAS_SLOAD :
  IsImported globals "ethereum.istanbul.vm.gas" "GAS_SLOAD".
Axiom ethereum_istanbul_vm_gas_imports_GAS_STORAGE_CLEAR_REFUND :
  IsImported globals "ethereum.istanbul.vm.gas" "GAS_STORAGE_CLEAR_REFUND".
Axiom ethereum_istanbul_vm_gas_imports_GAS_STORAGE_SET :
  IsImported globals "ethereum.istanbul.vm.gas" "GAS_STORAGE_SET".
Axiom ethereum_istanbul_vm_gas_imports_GAS_STORAGE_UPDATE :
  IsImported globals "ethereum.istanbul.vm.gas" "GAS_STORAGE_UPDATE".
Axiom ethereum_istanbul_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.istanbul.vm.gas" "charge_gas".

Axiom ethereum_istanbul_vm_stack_imports_pop :
  IsImported globals "ethereum.istanbul.vm.stack" "pop".
Axiom ethereum_istanbul_vm_stack_imports_push :
  IsImported globals "ethereum.istanbul.vm.stack" "push".

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
    let _ := M.assign_local (|
      "key" ,
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
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_SLOAD" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |)
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
    let _ := M.assign_local (|
      "key" ,
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
      |)
    |) in
    let _ := M.assign_local (|
      "new_value" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
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
    let _ := M.assign_local (|
      "original_value" ,
      M.call (|
        M.get_name (| globals, "get_storage_original" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "current_value" ,
      M.call (|
        M.get_name (| globals, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |)
    |) in
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
            let _ := M.assign_local (|
              "gas_cost" ,
              M.get_name (| globals, "GAS_STORAGE_SET" |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "gas_cost" ,
              M.get_name (| globals, "GAS_STORAGE_UPDATE" |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "gas_cost" ,
          M.get_name (| globals, "GAS_SLOAD" |)
        |) in
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
        M.get_name (| globals, "GAS_SLOAD" |)
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
        M.get_name (| globals, "GAS_STORAGE_UPDATE" |),
        M.get_name (| globals, "GAS_SLOAD" |)
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
