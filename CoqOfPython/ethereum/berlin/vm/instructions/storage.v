Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.berlin.vm.instructions.storage".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_berlin_state_imports_get_storage :
  IsImported globals "ethereum.berlin.state" "get_storage".
Axiom ethereum_berlin_state_imports_get_storage_original :
  IsImported globals "ethereum.berlin.state" "get_storage_original".
Axiom ethereum_berlin_state_imports_set_storage :
  IsImported globals "ethereum.berlin.state" "set_storage".

Axiom ethereum_berlin_vm_imports_Evm :
  IsImported globals "ethereum.berlin.vm" "Evm".

Axiom ethereum_berlin_vm_exceptions_imports_OutOfGasError :
  IsImported globals "ethereum.berlin.vm.exceptions" "OutOfGasError".
Axiom ethereum_berlin_vm_exceptions_imports_WriteInStaticContext :
  IsImported globals "ethereum.berlin.vm.exceptions" "WriteInStaticContext".

Axiom ethereum_berlin_vm_gas_imports_GAS_CALL_STIPEND :
  IsImported globals "ethereum.berlin.vm.gas" "GAS_CALL_STIPEND".
Axiom ethereum_berlin_vm_gas_imports_GAS_COLD_SLOAD :
  IsImported globals "ethereum.berlin.vm.gas" "GAS_COLD_SLOAD".
Axiom ethereum_berlin_vm_gas_imports_GAS_STORAGE_CLEAR_REFUND :
  IsImported globals "ethereum.berlin.vm.gas" "GAS_STORAGE_CLEAR_REFUND".
Axiom ethereum_berlin_vm_gas_imports_GAS_STORAGE_SET :
  IsImported globals "ethereum.berlin.vm.gas" "GAS_STORAGE_SET".
Axiom ethereum_berlin_vm_gas_imports_GAS_STORAGE_UPDATE :
  IsImported globals "ethereum.berlin.vm.gas" "GAS_STORAGE_UPDATE".
Axiom ethereum_berlin_vm_gas_imports_GAS_WARM_ACCESS :
  IsImported globals "ethereum.berlin.vm.gas" "GAS_WARM_ACCESS".
Axiom ethereum_berlin_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.berlin.vm.gas" "charge_gas".

Axiom ethereum_berlin_vm_stack_imports_pop :
  IsImported globals "ethereum.berlin.vm.stack" "pop".
Axiom ethereum_berlin_vm_stack_imports_push :
  IsImported globals "ethereum.berlin.vm.stack" "push".

Definition sload : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
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
          M.get_name (| globals, locals_stack, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.in_ (|
          make_tuple [ M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |); M.get_name (| globals, locals_stack, "key" |) ],
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "accessed_storage_keys" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_WARM_ACCESS" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "accessed_storage_keys" |), "add" |),
    make_list [
      make_tuple [ M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |); M.get_name (| globals, locals_stack, "key" |) ]
    ],
    make_dict []
  |) in
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_COLD_SLOAD" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, locals_stack, "key" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom sload_in_globals :
  IsInGlobals globals "sload" (make_function sload).

Definition sstore : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
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
          M.get_name (| globals, locals_stack, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
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
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |),
          M.get_name (| globals, locals_stack, "GAS_CALL_STIPEND" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "OutOfGasError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "original_value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_storage_original" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, locals_stack, "key" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "current_value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_storage" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
          M.get_name (| globals, locals_stack, "key" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "gas_cost" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_in (|
          make_tuple [ M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |); M.get_name (| globals, locals_stack, "key" |) ],
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "accessed_storage_keys" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "accessed_storage_keys" |), "add" |),
    make_list [
      make_tuple [ M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |); M.get_name (| globals, locals_stack, "key" |) ]
    ],
    make_dict []
  |) in
        let _ := M.assign_op_local (|
          BinOp.add,
          "gas_cost",
          M.get_name (| globals, locals_stack, "GAS_COLD_SLOAD" |)
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
          Compare.eq (|
            M.get_name (| globals, locals_stack, "original_value" |),
            M.get_name (| globals, locals_stack, "current_value" |)
          |),
          ltac:(M.monadic (
            Compare.not_eq (|
              M.get_name (| globals, locals_stack, "current_value" |),
              M.get_name (| globals, locals_stack, "new_value" |)
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_name (| globals, locals_stack, "original_value" |),
              Constant.int 0
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_op_local (|
              BinOp.add,
              "gas_cost",
              M.get_name (| globals, locals_stack, "GAS_STORAGE_SET" |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_op_local (|
              BinOp.add,
              "gas_cost",
              BinOp.sub (|
    M.get_name (| globals, locals_stack, "GAS_STORAGE_UPDATE" |),
    M.get_name (| globals, locals_stack, "GAS_COLD_SLOAD" |)
  |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_op_local (|
          BinOp.add,
          "gas_cost",
          M.get_name (| globals, locals_stack, "GAS_WARM_ACCESS" |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_name (| globals, locals_stack, "current_value" |),
          M.get_name (| globals, locals_stack, "new_value" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              Compare.not_eq (|
                M.get_name (| globals, locals_stack, "original_value" |),
                Constant.int 0
              |),
              ltac:(M.monadic (
                BoolOp.and (|
                  Compare.not_eq (|
                    M.get_name (| globals, locals_stack, "current_value" |),
                    Constant.int 0
                  |),
                  ltac:(M.monadic (
                    Compare.eq (|
                      M.get_name (| globals, locals_stack, "new_value" |),
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
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "refund_counter" |),
              M.call (|
    M.get_name (| globals, locals_stack, "int" |),
    make_list [
      M.get_name (| globals, locals_stack, "GAS_STORAGE_CLEAR_REFUND" |)
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
                M.get_name (| globals, locals_stack, "original_value" |),
                Constant.int 0
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_name (| globals, locals_stack, "current_value" |),
                  Constant.int 0
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_op (|
              BinOp.sub,
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "refund_counter" |),
              M.call (|
    M.get_name (| globals, locals_stack, "int" |),
    make_list [
      M.get_name (| globals, locals_stack, "GAS_STORAGE_CLEAR_REFUND" |)
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
              M.get_name (| globals, locals_stack, "original_value" |),
              M.get_name (| globals, locals_stack, "new_value" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.eq (|
                  M.get_name (| globals, locals_stack, "original_value" |),
                  Constant.int 0
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.assign_op (|
                  BinOp.add,
                  M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "refund_counter" |),
                  M.call (|
    M.get_name (| globals, locals_stack, "int" |),
    make_list [
      BinOp.sub (|
        M.get_name (| globals, locals_stack, "GAS_STORAGE_SET" |),
        M.get_name (| globals, locals_stack, "GAS_WARM_ACCESS" |)
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
                  M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "refund_counter" |),
                  M.call (|
    M.get_name (| globals, locals_stack, "int" |),
    make_list [
      BinOp.sub (|
        BinOp.sub (|
          M.get_name (| globals, locals_stack, "GAS_STORAGE_UPDATE" |),
          M.get_name (| globals, locals_stack, "GAS_COLD_SLOAD" |)
        |),
        M.get_name (| globals, locals_stack, "GAS_WARM_ACCESS" |)
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
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "gas_cost" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "is_static" |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "WriteInStaticContext" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_storage" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, locals_stack, "key" |);
      M.get_name (| globals, locals_stack, "new_value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom sstore_in_globals :
  IsInGlobals globals "sstore" (make_function sstore).
