Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.homestead.vm.instructions.system".

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

Axiom ethereum_homestead_fork_types_imports_Address :
  IsImported globals "ethereum.homestead.fork_types" "Address".

Axiom ethereum_homestead_state_imports_account_has_code_or_nonce :
  IsImported globals "ethereum.homestead.state" "account_has_code_or_nonce".
Axiom ethereum_homestead_state_imports_get_account :
  IsImported globals "ethereum.homestead.state" "get_account".
Axiom ethereum_homestead_state_imports_increment_nonce :
  IsImported globals "ethereum.homestead.state" "increment_nonce".
Axiom ethereum_homestead_state_imports_set_account_balance :
  IsImported globals "ethereum.homestead.state" "set_account_balance".

Axiom ethereum_homestead_utils_address_imports_compute_contract_address :
  IsImported globals "ethereum.homestead.utils.address" "compute_contract_address".
Axiom ethereum_homestead_utils_address_imports_to_address :
  IsImported globals "ethereum.homestead.utils.address" "to_address".

Axiom ethereum_homestead_vm_imports_Evm :
  IsImported globals "ethereum.homestead.vm" "Evm".
Axiom ethereum_homestead_vm_imports_Message :
  IsImported globals "ethereum.homestead.vm" "Message".
Axiom ethereum_homestead_vm_imports_incorporate_child_on_error :
  IsImported globals "ethereum.homestead.vm" "incorporate_child_on_error".
Axiom ethereum_homestead_vm_imports_incorporate_child_on_success :
  IsImported globals "ethereum.homestead.vm" "incorporate_child_on_success".

Axiom ethereum_homestead_vm_gas_imports_GAS_CALL :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_CALL".
Axiom ethereum_homestead_vm_gas_imports_GAS_CREATE :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_CREATE".
Axiom ethereum_homestead_vm_gas_imports_GAS_ZERO :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_ZERO".
Axiom ethereum_homestead_vm_gas_imports_REFUND_SELF_DESTRUCT :
  IsImported globals "ethereum.homestead.vm.gas" "REFUND_SELF_DESTRUCT".
Axiom ethereum_homestead_vm_gas_imports_calculate_gas_extend_memory :
  IsImported globals "ethereum.homestead.vm.gas" "calculate_gas_extend_memory".
Axiom ethereum_homestead_vm_gas_imports_calculate_message_call_gas :
  IsImported globals "ethereum.homestead.vm.gas" "calculate_message_call_gas".
Axiom ethereum_homestead_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.homestead.vm.gas" "charge_gas".

Axiom ethereum_homestead_vm_memory_imports_memory_read_bytes :
  IsImported globals "ethereum.homestead.vm.memory" "memory_read_bytes".
Axiom ethereum_homestead_vm_memory_imports_memory_write :
  IsImported globals "ethereum.homestead.vm.memory" "memory_write".

Axiom ethereum_homestead_vm_stack_imports_pop :
  IsImported globals "ethereum.homestead.vm.stack" "pop".
Axiom ethereum_homestead_vm_stack_imports_push :
  IsImported globals "ethereum.homestead.vm.stack" "push".

Definition create : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
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
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_start_position" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_start_position" |); M.get_name (| globals, "memory_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_name (| globals, "GAS_CREATE" |),
        M.get_field (| M.get_name (| globals, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "create_message_gas" ,
      M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.assign_local (|
      "sender_address" ,
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
    |) in
    let _ := M.assign_local (|
      "sender" ,
      M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "sender_address" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "contract_address" ,
      M.call (|
        M.get_name (| globals, "compute_contract_address" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
          M.get_field (| M.call (|
            M.get_name (| globals, "get_account" |),
            make_list [
              M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
              M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
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
            M.get_field (| M.get_name (| globals, "sender" |), "balance" |),
            M.get_name (| globals, "endowment" |)
          |),
          ltac:(M.monadic (
            BoolOp.or (|
              Compare.eq (|
                M.get_field (| M.get_name (| globals, "sender" |), "nonce" |),
                M.call (|
                  M.get_name (| globals, "Uint" |),
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
                    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "depth" |),
                    Constant.int 1
                  |),
                  M.get_name (| globals, "STACK_DEPTH_LIMIT" |)
                |)
              ))
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
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
          M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
          M.get_name (| globals, "create_message_gas" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, "account_has_code_or_nonce" |),
              make_list [
                M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
                M.get_name (| globals, "contract_address" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.call (|
    M.get_name (| globals, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
    ],
    make_dict []
  |) in
            let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
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
                M.get_name (| globals, "memory_read_bytes" |),
                make_list [
                  M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
                  M.get_name (| globals, "memory_start_position" |);
                  M.get_name (| globals, "memory_size" |)
                ],
                make_dict []
              |)
            |) in
            let _ := M.call (|
    M.get_name (| globals, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
    ],
    make_dict []
  |) in
            let _ := M.assign_local (|
              "child_message" ,
              M.call (|
                M.get_name (| globals, "Message" |),
                make_list [],
                make_dict []
              |)
            |) in
            let _ := M.assign_local (|
              "child_evm" ,
              M.call (|
                M.get_name (| globals, "process_create_message" |),
                make_list [
                  M.get_name (| globals, "child_message" |);
                  M.get_field (| M.get_name (| globals, "evm" |), "env" |)
                ],
                make_dict []
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                M.get_field (| M.get_name (| globals, "child_evm" |), "error" |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.call (|
    M.get_name (| globals, "incorporate_child_on_error" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "child_evm" |)
    ],
    make_dict []
  |) in
                let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
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
    M.get_name (| globals, "incorporate_child_on_success" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "child_evm" |)
    ],
    make_dict []
  |) in
                let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "child_evm" |), "message" |), "current_target" |)
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
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition return_ : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
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
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_start_position" |); M.get_name (| globals, "memory_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_name (| globals, "GAS_ZERO" |),
        M.get_field (| M.get_name (| globals, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      M.call (|
        M.get_name (| globals, "memory_read_bytes" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          M.get_name (| globals, "memory_start_position" |);
          M.get_name (| globals, "memory_size" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "running" |),
      Constant.bool false
    |) in
    let _ := M.pass (| |) in
    M.pure Constant.None_)).

Definition generic_call : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "gas"; "value"; "caller"; "to"; "code_address"; "should_transfer_value"; "memory_input_start_position"; "memory_input_size"; "memory_output_start_position"; "memory_output_size" ] |) in
    let _ := Constant.str "
    Perform the core logic of the `CALL*` family of opcodes.
    " in
(* At stmt: unsupported node type: ImportFrom *)
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          BinOp.add (|
            M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "depth" |),
            Constant.int 1
          |),
          M.get_name (| globals, "STACK_DEPTH_LIMIT" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
          M.get_name (| globals, "gas" |)
        |) in
        let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
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
        M.get_name (| globals, "memory_read_bytes" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          M.get_name (| globals, "memory_input_start_position" |);
          M.get_name (| globals, "memory_input_size" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "code" ,
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "code_address" |)
        ],
        make_dict []
      |), "code" |)
    |) in
    let _ := M.assign_local (|
      "child_message" ,
      M.call (|
        M.get_name (| globals, "Message" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "child_evm" ,
      M.call (|
        M.get_name (| globals, "process_message" |),
        make_list [
          M.get_name (| globals, "child_message" |);
          M.get_field (| M.get_name (| globals, "evm" |), "env" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.get_field (| M.get_name (| globals, "child_evm" |), "error" |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "incorporate_child_on_error" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "child_evm" |)
    ],
    make_dict []
  |) in
        let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
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
    M.get_name (| globals, "incorporate_child_on_success" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "child_evm" |)
    ],
    make_dict []
  |) in
        let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
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
        M.get_name (| globals, "min" |),
        make_list [
          M.get_name (| globals, "memory_output_size" |);
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              M.call (|
                M.get_name (| globals, "len" |),
                make_list [
                  M.get_field (| M.get_name (| globals, "child_evm" |), "output" |)
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
    M.get_name (| globals, "memory_write" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
      M.get_name (| globals, "memory_output_start_position" |);
      M.slice (|
        M.get_field (| M.get_name (| globals, "child_evm" |), "output" |),
        Constant.None_,
        M.get_name (| globals, "actual_output_size" |),
        Constant.None_
      |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition call : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
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
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
        M.get_name (| globals, "to_address" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_start_position" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_start_position" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_input_start_position" |); M.get_name (| globals, "memory_input_size" |) ];
            make_tuple [ M.get_name (| globals, "memory_output_start_position" |); M.get_name (| globals, "memory_output_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "message_call_gas" ,
      M.call (|
        M.get_name (| globals, "calculate_message_call_gas" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "gas" |);
          M.get_name (| globals, "to" |);
          M.get_name (| globals, "value" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_field (| M.get_name (| globals, "message_call_gas" |), "cost" |),
        M.get_field (| M.get_name (| globals, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.assign_local (|
      "sender_balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, "sender_balance" |),
          M.get_name (| globals, "value" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
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
          M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
          M.get_field (| M.get_name (| globals, "message_call_gas" |), "stipend" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "generic_call" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_field (| M.get_name (| globals, "message_call_gas" |), "stipend" |);
      M.get_name (| globals, "value" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, "to" |);
      M.get_name (| globals, "to" |);
      Constant.bool true;
      M.get_name (| globals, "memory_input_start_position" |);
      M.get_name (| globals, "memory_input_size" |);
      M.get_name (| globals, "memory_output_start_position" |);
      M.get_name (| globals, "memory_output_size" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition callcode : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
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
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
        M.get_name (| globals, "to_address" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_start_position" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_start_position" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "to" ,
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_input_start_position" |); M.get_name (| globals, "memory_input_size" |) ];
            make_tuple [ M.get_name (| globals, "memory_output_start_position" |); M.get_name (| globals, "memory_output_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "message_call_gas" ,
      M.call (|
        M.get_name (| globals, "calculate_message_call_gas" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "gas" |);
          M.get_name (| globals, "to" |);
          M.get_name (| globals, "value" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_field (| M.get_name (| globals, "message_call_gas" |), "cost" |),
        M.get_field (| M.get_name (| globals, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.assign_local (|
      "sender_balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, "sender_balance" |),
          M.get_name (| globals, "value" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_name (| globals, "U256" |),
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
          M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
          M.get_field (| M.get_name (| globals, "message_call_gas" |), "stipend" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "generic_call" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_field (| M.get_name (| globals, "message_call_gas" |), "stipend" |);
      M.get_name (| globals, "value" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, "to" |);
      M.get_name (| globals, "code_address" |);
      Constant.bool true;
      M.get_name (| globals, "memory_input_start_position" |);
      M.get_name (| globals, "memory_input_size" |);
      M.get_name (| globals, "memory_output_start_position" |);
      M.get_name (| globals, "memory_output_size" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition selfdestruct : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
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
        M.get_name (| globals, "to_address" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "gas_cost" ,
      M.get_name (| globals, "GAS_ZERO" |)
    |) in
    let _ := M.assign_local (|
      "originator" ,
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
    |) in
    let _ := M.assign_local (|
      "refunded_accounts" ,
      M.get_field (| M.get_name (| globals, "evm" |), "accounts_to_delete" |)
    |) in
    let _ := M.assign_local (|
      "parent_evm" ,
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "parent_evm" |)
    |) in
    let _ :=
      M.while (|
        Compare.is_not (|
      M.get_name (| globals, "parent_evm" |),
      Constant.None_
    |),
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, "refunded_accounts" |), "update" |),
    make_list [
      M.get_field (| M.get_name (| globals, "parent_evm" |), "accounts_to_delete" |)
    ],
    make_dict []
  |) in
          let _ := M.assign_local (|
            "parent_evm" ,
            M.get_field (| M.get_field (| M.get_name (| globals, "parent_evm" |), "message" |), "parent_evm" |)
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
          M.get_name (| globals, "originator" |),
          M.get_name (| globals, "refunded_accounts" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_op (|
          BinOp.add,
          M.get_field (| M.get_name (| globals, "evm" |), "refund_counter" |),
          M.get_name (| globals, "REFUND_SELF_DESTRUCT" |)
        |) in
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
    let _ := M.assign_local (|
      "beneficiary_balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "beneficiary" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ := M.assign_local (|
      "originator_balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "originator" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
      M.get_name (| globals, "beneficiary" |);
      BinOp.add (|
        M.get_name (| globals, "beneficiary_balance" |),
        M.get_name (| globals, "originator_balance" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
      M.get_name (| globals, "originator" |);
      M.call (|
        M.get_name (| globals, "U256" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "accounts_to_delete" |), "add" |),
    make_list [
      M.get_name (| globals, "originator" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "running" |),
      Constant.bool false
    |) in
    let _ := M.pass (| |) in
    M.pure Constant.None_)).

Definition delegatecall : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
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
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
        M.get_name (| globals, "to_address" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_input_size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_start_position" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "memory_output_size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_input_start_position" |); M.get_name (| globals, "memory_input_size" |) ];
            make_tuple [ M.get_name (| globals, "memory_output_start_position" |); M.get_name (| globals, "memory_output_size" |) ]
          ]
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        BinOp.add (|
          M.get_name (| globals, "GAS_CALL" |),
          M.get_name (| globals, "gas" |)
        |),
        M.get_field (| M.get_name (| globals, "extend_memory" |), "cost" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "generic_call" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "gas" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "value" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "caller" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |);
      M.get_name (| globals, "code_address" |);
      Constant.bool false;
      M.get_name (| globals, "memory_input_start_position" |);
      M.get_name (| globals, "memory_input_size" |);
      M.get_name (| globals, "memory_output_start_position" |);
      M.get_name (| globals, "memory_output_size" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).
