Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.spurious_dragon.vm.instructions.system".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) System Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM system related instructions.
".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_spurious_dragon_fork_types_imports_Address :
  IsImported globals "ethereum.spurious_dragon.fork_types" "Address".

Axiom ethereum_spurious_dragon_state_imports_account_exists_and_is_empty :
  IsImported globals "ethereum.spurious_dragon.state" "account_exists_and_is_empty".
Axiom ethereum_spurious_dragon_state_imports_account_has_code_or_nonce :
  IsImported globals "ethereum.spurious_dragon.state" "account_has_code_or_nonce".
Axiom ethereum_spurious_dragon_state_imports_get_account :
  IsImported globals "ethereum.spurious_dragon.state" "get_account".
Axiom ethereum_spurious_dragon_state_imports_increment_nonce :
  IsImported globals "ethereum.spurious_dragon.state" "increment_nonce".
Axiom ethereum_spurious_dragon_state_imports_is_account_alive :
  IsImported globals "ethereum.spurious_dragon.state" "is_account_alive".
Axiom ethereum_spurious_dragon_state_imports_set_account_balance :
  IsImported globals "ethereum.spurious_dragon.state" "set_account_balance".

Axiom ethereum_spurious_dragon_utils_address_imports_compute_contract_address :
  IsImported globals "ethereum.spurious_dragon.utils.address" "compute_contract_address".
Axiom ethereum_spurious_dragon_utils_address_imports_to_address :
  IsImported globals "ethereum.spurious_dragon.utils.address" "to_address".

Axiom ethereum_spurious_dragon_vm_imports_Evm :
  IsImported globals "ethereum.spurious_dragon.vm" "Evm".
Axiom ethereum_spurious_dragon_vm_imports_Message :
  IsImported globals "ethereum.spurious_dragon.vm" "Message".
Axiom ethereum_spurious_dragon_vm_imports_incorporate_child_on_error :
  IsImported globals "ethereum.spurious_dragon.vm" "incorporate_child_on_error".
Axiom ethereum_spurious_dragon_vm_imports_incorporate_child_on_success :
  IsImported globals "ethereum.spurious_dragon.vm" "incorporate_child_on_success".

Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_CALL :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_CALL".
Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_CALL_VALUE :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_CALL_VALUE".
Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_CREATE :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_CREATE".
Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_NEW_ACCOUNT :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_NEW_ACCOUNT".
Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_SELF_DESTRUCT :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_SELF_DESTRUCT".
Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_SELF_DESTRUCT_NEW_ACCOUNT :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_SELF_DESTRUCT_NEW_ACCOUNT".
Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_ZERO :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_ZERO".
Axiom ethereum_spurious_dragon_vm_gas_imports_REFUND_SELF_DESTRUCT :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "REFUND_SELF_DESTRUCT".
Axiom ethereum_spurious_dragon_vm_gas_imports_calculate_gas_extend_memory :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "calculate_gas_extend_memory".
Axiom ethereum_spurious_dragon_vm_gas_imports_calculate_message_call_gas :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "calculate_message_call_gas".
Axiom ethereum_spurious_dragon_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "charge_gas".
Axiom ethereum_spurious_dragon_vm_gas_imports_max_message_call_gas :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "max_message_call_gas".

Axiom ethereum_spurious_dragon_vm_memory_imports_memory_read_bytes :
  IsImported globals "ethereum.spurious_dragon.vm.memory" "memory_read_bytes".
Axiom ethereum_spurious_dragon_vm_memory_imports_memory_write :
  IsImported globals "ethereum.spurious_dragon.vm.memory" "memory_write".

Axiom ethereum_spurious_dragon_vm_stack_imports_pop :
  IsImported globals "ethereum.spurious_dragon.vm.stack" "pop".
Axiom ethereum_spurious_dragon_vm_stack_imports_push :
  IsImported globals "ethereum.spurious_dragon.vm.stack" "push".

Definition create : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Creates a new account with associated code.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
(* At stmt: unsupported node type: ImportFrom *)
    let _ := M.assign_local (|
      "endowment" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_start_position" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, locals_stack, "memory_start_position" |); M.get_name (| globals, locals_stack, "memory_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.add (|
        M.get_name (| globals, locals_stack, "GAS_CREATE" |),
        M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "create_message_gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "max_message_call_gas" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_op (|
      BinOp.sub,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |),
      M.get_name (| globals, locals_stack, "create_message_gas" |)
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.assign_local (|
      "sender_address" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
    |) in
    let _ := M.assign_local (|
      "sender" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_name (| globals, locals_stack, "sender_address" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "contract_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "compute_contract_address" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
          M.get_field (| M.call (|
            M.get_name (| globals, locals_stack, "get_account" |),
            make_list [
              M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
              M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
            ],
            make_dict []
          |), "nonce" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.lt (|
            M.get_field (| M.get_name (| globals, locals_stack, "sender" |), "balance" |),
            M.get_name (| globals, locals_stack, "endowment" |)
          |),
          ltac:(M.monadic (
            BoolOp.or (|
              Compare.eq (|
                M.get_field (| M.get_name (| globals, locals_stack, "sender" |), "nonce" |),
                M.call (|
                  M.get_name (| globals, locals_stack, "Uint" |),
                  make_list [
                    BinOp.sub (|
                      BinOp.pow (|
                        Constant.int 2,
                        Constant.int 64
                      |),
                      Constant.int 1
                    |)
                  ],
                  make_dict []
                |)
              |),
              ltac:(M.monadic (
                Compare.gt (|
                  BinOp.add (|
                    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "depth" |),
                    Constant.int 1
                  |),
                  M.get_name (| globals, locals_stack, "STACK_DEPTH_LIMIT" |)
                |)
              ))
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |),
          M.get_name (| globals, locals_stack, "create_message_gas" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, locals_stack, "account_has_code_or_nonce" |),
              make_list [
                M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
                M.get_name (| globals, locals_stack, "contract_address" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.call (|
    M.get_name (| globals, locals_stack, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
    ],
    make_dict []
  |) in
            let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "call_data" ,
              M.call (|
                M.get_name (| globals, locals_stack, "memory_read_bytes" |),
                make_list [
                  M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
                  M.get_name (| globals, locals_stack, "memory_start_position" |);
                  M.get_name (| globals, locals_stack, "memory_size" |)
                ],
                make_dict []
              |)
            |) in
            let _ := M.call (|
    M.get_name (| globals, locals_stack, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
    ],
    make_dict []
  |) in
            let _ := M.assign_local (|
              "child_message" ,
              M.call (|
                M.get_name (| globals, locals_stack, "Message" |),
                make_list [],
                make_dict []
              |)
            |) in
            let _ := M.assign_local (|
              "child_evm" ,
              M.call (|
                M.get_name (| globals, locals_stack, "process_create_message" |),
                make_list [
                  M.get_name (| globals, locals_stack, "child_message" |);
                  M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |)
                ],
                make_dict []
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                M.get_field (| M.get_name (| globals, locals_stack, "child_evm" |), "error" |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.call (|
    M.get_name (| globals, locals_stack, "incorporate_child_on_error" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "child_evm" |)
    ],
    make_dict []
  |) in
                let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ := M.call (|
    M.get_name (| globals, locals_stack, "incorporate_child_on_success" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "child_evm" |)
    ],
    make_dict []
  |) in
                let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "child_evm" |), "message" |), "current_target" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom create_in_globals :
  IsInGlobals globals "create" (make_function create).

Definition return_ : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Halts execution returning output data.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "memory_start_position" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, locals_stack, "memory_start_position" |); M.get_name (| globals, locals_stack, "memory_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.add (|
        M.get_name (| globals, locals_stack, "GAS_ZERO" |),
        M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
      M.call (|
        M.get_name (| globals, locals_stack, "memory_read_bytes" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          M.get_name (| globals, locals_stack, "memory_start_position" |);
          M.get_name (| globals, locals_stack, "memory_size" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "running" |),
      Constant.bool false
    |) in
    let _ := M.pass (| |) in
    M.pure Constant.None_)).

Axiom return__in_globals :
  IsInGlobals globals "return_" (make_function return_).

Definition generic_call : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm"; "gas"; "value"; "caller"; "to"; "code_address"; "should_transfer_value"; "memory_input_start_position"; "memory_input_size"; "memory_output_start_position"; "memory_output_size" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Perform the core logic of the `CALL*` family of opcodes.
    " in
(* At stmt: unsupported node type: ImportFrom *)
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          BinOp.add (|
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "depth" |),
            Constant.int 1
          |),
          M.get_name (| globals, locals_stack, "STACK_DEPTH_LIMIT" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |),
          M.get_name (| globals, locals_stack, "gas" |)
        |) in
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
        let _ := M.return_ (|
          Constant.None_
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "call_data" ,
      M.call (|
        M.get_name (| globals, locals_stack, "memory_read_bytes" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          M.get_name (| globals, locals_stack, "memory_input_start_position" |);
          M.get_name (| globals, locals_stack, "memory_input_size" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "code" ,
      M.get_field (| M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_name (| globals, locals_stack, "code_address" |)
        ],
        make_dict []
      |), "code" |)
    |) in
    let _ := M.assign_local (|
      "child_message" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Message" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "child_evm" ,
      M.call (|
        M.get_name (| globals, locals_stack, "process_message" |),
        make_list [
          M.get_name (| globals, locals_stack, "child_message" |);
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.get_field (| M.get_name (| globals, locals_stack, "child_evm" |), "error" |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "incorporate_child_on_error" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "child_evm" |)
    ],
    make_dict []
  |) in
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "incorporate_child_on_success" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "child_evm" |)
    ],
    make_dict []
  |) in
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 1
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "actual_output_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "min" |),
        make_list [
          M.get_name (| globals, locals_stack, "memory_output_size" |);
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "len" |),
                make_list [
                  M.get_field (| M.get_name (| globals, locals_stack, "child_evm" |), "output" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "memory_write" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
      M.get_name (| globals, locals_stack, "memory_output_start_position" |);
      M.slice (|
        M.get_field (| M.get_name (| globals, locals_stack, "child_evm" |), "output" |),
        Constant.None_,
        M.get_name (| globals, locals_stack, "actual_output_size" |),
        Constant.None_
      |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom generic_call_in_globals :
  IsInGlobals globals "generic_call" (make_function generic_call).

Definition call : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Message-call into an account.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "to" ,
      M.call (|
        M.get_name (| globals, locals_stack, "to_address" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_start_position" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_start_position" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, locals_stack, "memory_input_start_position" |); M.get_name (| globals, locals_stack, "memory_input_size" |) ];
            make_tuple [ M.get_name (| globals, locals_stack, "memory_output_start_position" |); M.get_name (| globals, locals_stack, "memory_output_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "create_gas_cost" ,
            (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.eq (|
            M.get_name (| globals, locals_stack, "value" |),
            Constant.int 0
          |),
          ltac:(M.monadic (
            M.call (|
              M.get_name (| globals, locals_stack, "is_account_alive" |),
              make_list [
                M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
                M.get_name (| globals, locals_stack, "to" |)
              ],
              make_dict []
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
M.call (|
          M.get_name (| globals, locals_stack, "Uint" |),
          make_list [
            Constant.int 0
          ],
          make_dict []
        |)
      (* else *)
      )), ltac:(M.monadic (
M.get_name (| globals, locals_stack, "GAS_NEW_ACCOUNT" |)
      )) |)
    |) in
    let _ := M.assign_local (|
      "transfer_gas_cost" ,
            (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "value" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
M.call (|
          M.get_name (| globals, locals_stack, "Uint" |),
          make_list [
            Constant.int 0
          ],
          make_dict []
        |)
      (* else *)
      )), ltac:(M.monadic (
M.get_name (| globals, locals_stack, "GAS_CALL_VALUE" |)
      )) |)
    |) in
    let _ := M.assign_local (|
      "message_call_gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_message_call_gas" |),
        make_list [
          M.get_name (| globals, locals_stack, "value" |);
          M.get_name (| globals, locals_stack, "gas" |);
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |)
            ],
            make_dict []
          |);
          M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "cost" |);
          BinOp.add (|
            BinOp.add (|
              M.get_name (| globals, locals_stack, "GAS_CALL" |),
              M.get_name (| globals, locals_stack, "create_gas_cost" |)
            |),
            M.get_name (| globals, locals_stack, "transfer_gas_cost" |)
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.add (|
        M.get_field (| M.get_name (| globals, locals_stack, "message_call_gas" |), "cost" |),
        M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.assign_local (|
      "sender_balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, locals_stack, "sender_balance" |),
          M.get_name (| globals, locals_stack, "value" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |),
          M.get_field (| M.get_name (| globals, locals_stack, "message_call_gas" |), "stipend" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "generic_call" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message_call_gas" |), "stipend" |);
      M.get_name (| globals, locals_stack, "value" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, locals_stack, "to" |);
      M.get_name (| globals, locals_stack, "to" |);
      Constant.bool true;
      M.get_name (| globals, locals_stack, "memory_input_start_position" |);
      M.get_name (| globals, locals_stack, "memory_input_size" |);
      M.get_name (| globals, locals_stack, "memory_output_start_position" |);
      M.get_name (| globals, locals_stack, "memory_output_size" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom call_in_globals :
  IsInGlobals globals "call" (make_function call).

Definition callcode : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Message-call into this account with alternative account’s code.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "code_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "to_address" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_start_position" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_start_position" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "to" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, locals_stack, "memory_input_start_position" |); M.get_name (| globals, locals_stack, "memory_input_size" |) ];
            make_tuple [ M.get_name (| globals, locals_stack, "memory_output_start_position" |); M.get_name (| globals, locals_stack, "memory_output_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "transfer_gas_cost" ,
            (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "value" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
M.call (|
          M.get_name (| globals, locals_stack, "Uint" |),
          make_list [
            Constant.int 0
          ],
          make_dict []
        |)
      (* else *)
      )), ltac:(M.monadic (
M.get_name (| globals, locals_stack, "GAS_CALL_VALUE" |)
      )) |)
    |) in
    let _ := M.assign_local (|
      "message_call_gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_message_call_gas" |),
        make_list [
          M.get_name (| globals, locals_stack, "value" |);
          M.get_name (| globals, locals_stack, "gas" |);
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |)
            ],
            make_dict []
          |);
          M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "cost" |);
          BinOp.add (|
            M.get_name (| globals, locals_stack, "GAS_CALL" |),
            M.get_name (| globals, locals_stack, "transfer_gas_cost" |)
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.add (|
        M.get_field (| M.get_name (| globals, locals_stack, "message_call_gas" |), "cost" |),
        M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.assign_local (|
      "sender_balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, locals_stack, "sender_balance" |),
          M.get_name (| globals, locals_stack, "value" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |),
          M.get_field (| M.get_name (| globals, locals_stack, "message_call_gas" |), "stipend" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "generic_call" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message_call_gas" |), "stipend" |);
      M.get_name (| globals, locals_stack, "value" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, locals_stack, "to" |);
      M.get_name (| globals, locals_stack, "code_address" |);
      Constant.bool true;
      M.get_name (| globals, locals_stack, "memory_input_start_position" |);
      M.get_name (| globals, locals_stack, "memory_input_size" |);
      M.get_name (| globals, locals_stack, "memory_output_start_position" |);
      M.get_name (| globals, locals_stack, "memory_output_size" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom callcode_in_globals :
  IsInGlobals globals "callcode" (make_function callcode).

Definition selfdestruct : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Halt execution and register account for later deletion.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "beneficiary" ,
      M.call (|
        M.get_name (| globals, locals_stack, "to_address" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "gas_cost" ,
      M.get_name (| globals, locals_stack, "GAS_SELF_DESTRUCT" |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          UnOp.not (| M.call (|
            M.get_name (| globals, locals_stack, "is_account_alive" |),
            make_list [
              M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
              M.get_name (| globals, locals_stack, "beneficiary" |)
            ],
            make_dict []
          |) |),
          ltac:(M.monadic (
            Compare.not_eq (|
              M.get_field (| M.call (|
                M.get_name (| globals, locals_stack, "get_account" |),
                make_list [
                  M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
                  M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
                ],
                make_dict []
              |), "balance" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_op_local (|
          BinOp.add,
          "gas_cost",
          M.get_name (| globals, locals_stack, "GAS_SELF_DESTRUCT_NEW_ACCOUNT" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "originator" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
    |) in
    let _ := M.assign_local (|
      "refunded_accounts" ,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "accounts_to_delete" |)
    |) in
    let _ := M.assign_local (|
      "parent_evm" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "parent_evm" |)
    |) in
    let _ :=
      M.while (|
        Compare.is_not (|
      M.get_name (| globals, locals_stack, "parent_evm" |),
      Constant.None_
    |),
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "refunded_accounts" |), "update" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "parent_evm" |), "accounts_to_delete" |)
    ],
    make_dict []
  |) in
          let _ := M.assign_local (|
            "parent_evm" ,
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "parent_evm" |), "message" |), "parent_evm" |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_in (|
          M.get_name (| globals, locals_stack, "originator" |),
          M.get_name (| globals, locals_stack, "refunded_accounts" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "refund_counter" |),
          M.get_name (| globals, locals_stack, "REFUND_SELF_DESTRUCT" |)
        |) in
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
    let _ := M.assign_local (|
      "beneficiary_balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_name (| globals, locals_stack, "beneficiary" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ := M.assign_local (|
      "originator_balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_name (| globals, locals_stack, "originator" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
      M.get_name (| globals, locals_stack, "beneficiary" |);
      BinOp.add (|
        M.get_name (| globals, locals_stack, "beneficiary_balance" |),
        M.get_name (| globals, locals_stack, "originator_balance" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
      M.get_name (| globals, locals_stack, "originator" |);
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "accounts_to_delete" |), "add" |),
    make_list [
      M.get_name (| globals, locals_stack, "originator" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "account_exists_and_is_empty" |),
          make_list [
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
            M.get_name (| globals, locals_stack, "beneficiary" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "touched_accounts" |), "add" |),
    make_list [
      M.get_name (| globals, locals_stack, "beneficiary" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "running" |),
      Constant.bool false
    |) in
    let _ := M.pass (| |) in
    M.pure Constant.None_)).

Axiom selfdestruct_in_globals :
  IsInGlobals globals "selfdestruct" (make_function selfdestruct).

Definition delegatecall : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Message-call into an account.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "code_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "to_address" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_start_position" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_start_position" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, locals_stack, "memory_input_start_position" |); M.get_name (| globals, locals_stack, "memory_input_size" |) ];
            make_tuple [ M.get_name (| globals, locals_stack, "memory_output_start_position" |); M.get_name (| globals, locals_stack, "memory_output_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "message_call_gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_message_call_gas" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |);
          M.get_name (| globals, locals_stack, "gas" |);
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |)
            ],
            make_dict []
          |);
          M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "cost" |);
          M.get_name (| globals, locals_stack, "GAS_CALL" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.add (|
        M.get_field (| M.get_name (| globals, locals_stack, "message_call_gas" |), "cost" |),
        M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, locals_stack, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "generic_call" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message_call_gas" |), "stipend" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "value" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "caller" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, locals_stack, "code_address" |);
      Constant.bool false;
      M.get_name (| globals, locals_stack, "memory_input_start_position" |);
      M.get_name (| globals, locals_stack, "memory_input_size" |);
      M.get_name (| globals, locals_stack, "memory_output_start_position" |);
      M.get_name (| globals, locals_stack, "memory_output_size" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom delegatecall_in_globals :
  IsInGlobals globals "delegatecall" (make_function delegatecall).
