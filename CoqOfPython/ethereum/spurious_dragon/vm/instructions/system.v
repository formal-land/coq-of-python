Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes0 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes0".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require fork_types.
Axiom fork_types_Address :
  IsGlobalAlias globals fork_types.globals "Address".

Require state.
Axiom state_account_exists_and_is_empty :
  IsGlobalAlias globals state.globals "account_exists_and_is_empty".
Axiom state_account_has_code_or_nonce :
  IsGlobalAlias globals state.globals "account_has_code_or_nonce".
Axiom state_get_account :
  IsGlobalAlias globals state.globals "get_account".
Axiom state_increment_nonce :
  IsGlobalAlias globals state.globals "increment_nonce".
Axiom state_is_account_alive :
  IsGlobalAlias globals state.globals "is_account_alive".
Axiom state_set_account_balance :
  IsGlobalAlias globals state.globals "set_account_balance".

Require utils.address.
Axiom utils_address_compute_contract_address :
  IsGlobalAlias globals utils.address.globals "compute_contract_address".
Axiom utils_address_to_address :
  IsGlobalAlias globals utils.address.globals "to_address".

Require __init__.
Axiom __init___Evm :
  IsGlobalAlias globals __init__.globals "Evm".
Axiom __init___Message :
  IsGlobalAlias globals __init__.globals "Message".
Axiom __init___incorporate_child_on_error :
  IsGlobalAlias globals __init__.globals "incorporate_child_on_error".
Axiom __init___incorporate_child_on_success :
  IsGlobalAlias globals __init__.globals "incorporate_child_on_success".

Require gas.
Axiom gas_GAS_CALL :
  IsGlobalAlias globals gas.globals "GAS_CALL".
Axiom gas_GAS_CALL_VALUE :
  IsGlobalAlias globals gas.globals "GAS_CALL_VALUE".
Axiom gas_GAS_CREATE :
  IsGlobalAlias globals gas.globals "GAS_CREATE".
Axiom gas_GAS_NEW_ACCOUNT :
  IsGlobalAlias globals gas.globals "GAS_NEW_ACCOUNT".
Axiom gas_GAS_SELF_DESTRUCT :
  IsGlobalAlias globals gas.globals "GAS_SELF_DESTRUCT".
Axiom gas_GAS_SELF_DESTRUCT_NEW_ACCOUNT :
  IsGlobalAlias globals gas.globals "GAS_SELF_DESTRUCT_NEW_ACCOUNT".
Axiom gas_GAS_ZERO :
  IsGlobalAlias globals gas.globals "GAS_ZERO".
Axiom gas_REFUND_SELF_DESTRUCT :
  IsGlobalAlias globals gas.globals "REFUND_SELF_DESTRUCT".
Axiom gas_calculate_gas_extend_memory :
  IsGlobalAlias globals gas.globals "calculate_gas_extend_memory".
Axiom gas_calculate_message_call_gas :
  IsGlobalAlias globals gas.globals "calculate_message_call_gas".
Axiom gas_charge_gas :
  IsGlobalAlias globals gas.globals "charge_gas".
Axiom gas_max_message_call_gas :
  IsGlobalAlias globals gas.globals "max_message_call_gas".

Require memory.
Axiom memory_memory_read_bytes :
  IsGlobalAlias globals memory.globals "memory_read_bytes".
Axiom memory_memory_write :
  IsGlobalAlias globals memory.globals "memory_write".

Require stack.
Axiom stack_pop :
  IsGlobalAlias globals stack.globals "pop".
Axiom stack_push :
  IsGlobalAlias globals stack.globals "push".

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
    let endowment :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let extend_memory :=
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_start_position" |); M.get_name (| globals, "memory_size" |) ]
          ]
        ],
        make_dict []
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
    let create_message_gas :=
      M.call (|
        M.get_name (| globals, "max_message_call_gas" |),
        make_list [
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ := M.assign_op (|
      BinOp.sub,
      M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
      M.get_name (| globals, "create_message_gas" |)
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |),
      BinOp.mult (|
    Constant.bytes "00",
    M.get_field (| M.get_name (| globals, "extend_memory" |), "expand_by" |)
  |)
    |) in
    let sender_address :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |) in
    let sender :=
      M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "sender_address" |)
        ],
        make_dict []
      |) in
    let contract_address :=
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
      |) in
    let _ :=
        let _ :=
            let call_data :=
              M.call (|
                M.get_name (| globals, "memory_read_bytes" |),
                make_list [
                  M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
                  M.get_name (| globals, "memory_start_position" |);
                  M.get_name (| globals, "memory_size" |)
                ],
                make_dict []
              |) in
            let _ := M.call (|
    M.get_name (| globals, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
    ],
    make_dict []
  |) in
            let child_message :=
              M.call (|
                M.get_name (| globals, "Message" |),
                make_list [],
                make_dict []
              |) in
            let child_evm :=
              M.call (|
                M.get_name (| globals, "process_create_message" |),
                make_list [
                  M.get_name (| globals, "child_message" |);
                  M.get_field (| M.get_name (| globals, "evm" |), "env" |)
                ],
                make_dict []
              |) in
            let _ :=
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
    let memory_start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let extend_memory :=
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_start_position" |); M.get_name (| globals, "memory_size" |) ]
          ]
        ],
        make_dict []
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
        M.pure Constant.None_
      )) |) in
    let call_data :=
      M.call (|
        M.get_name (| globals, "memory_read_bytes" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          M.get_name (| globals, "memory_input_start_position" |);
          M.get_name (| globals, "memory_input_size" |)
        ],
        make_dict []
      |) in
    let code :=
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "code_address" |)
        ],
        make_dict []
      |), "code" |) in
    let child_message :=
      M.call (|
        M.get_name (| globals, "Message" |),
        make_list [],
        make_dict []
      |) in
    let child_evm :=
      M.call (|
        M.get_name (| globals, "process_message" |),
        make_list [
          M.get_name (| globals, "child_message" |);
          M.get_field (| M.get_name (| globals, "evm" |), "env" |)
        ],
        make_dict []
      |) in
    let _ :=
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
    let actual_output_size :=
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
      |) in
    let _ := M.call (|
    M.get_name (| globals, "memory_write" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
      M.get_name (| globals, "memory_output_start_position" |);
      M.get_subscript (| M.get_field (| M.get_name (| globals, "child_evm" |), "output" |), Constant.None_:M.get_name (| globals, "actual_output_size" |) |)
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
    let gas :=
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
      |) in
    let to :=
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
      |) in
    let value :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_input_start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_input_size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_output_start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_output_size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let extend_memory :=
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
      |) in
    let create_gas_cost :=
      (* if *)
M.if_then_else (|
  BoolOp.or (|
    Compare.eq (|
      M.get_name (| globals, "value" |),
      Constant.int 0
    |),
    ltac:(M.monadic (
      M.call (|
        M.get_name (| globals, "is_account_alive" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "to" |)
        ],
        make_dict []
      |)
    ))
  |),
(* then *)
ltac:(M.monadic (
M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 0
    ],
    make_dict []
  |) in
    let transfer_gas_cost :=
      (* if *)
M.if_then_else (|
  Compare.eq (|
    M.get_name (| globals, "value" |),
    Constant.int 0
  |),
(* then *)
ltac:(M.monadic (
M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 0
    ],
    make_dict []
  |) in
    let message_call_gas :=
      M.call (|
        M.get_name (| globals, "calculate_message_call_gas" |),
        make_list [
          M.get_name (| globals, "value" |);
          M.get_name (| globals, "gas" |);
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |)
            ],
            make_dict []
          |);
          M.get_field (| M.get_name (| globals, "extend_memory" |), "cost" |);
          BinOp.add (|
            BinOp.add (|
              M.get_name (| globals, "GAS_CALL" |),
              M.get_name (| globals, "create_gas_cost" |)
            |),
            M.get_name (| globals, "transfer_gas_cost" |)
          |)
        ],
        make_dict []
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
    let sender_balance :=
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
        ],
        make_dict []
      |), "balance" |) in
    let _ :=
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
    let gas :=
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
      |) in
    let code_address :=
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
      |) in
    let value :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_input_start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_input_size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_output_start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_output_size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let to :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |) in
    let extend_memory :=
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
      |) in
    let transfer_gas_cost :=
      (* if *)
M.if_then_else (|
  Compare.eq (|
    M.get_name (| globals, "value" |),
    Constant.int 0
  |),
(* then *)
ltac:(M.monadic (
M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 0
    ],
    make_dict []
  |) in
    let message_call_gas :=
      M.call (|
        M.get_name (| globals, "calculate_message_call_gas" |),
        make_list [
          M.get_name (| globals, "value" |);
          M.get_name (| globals, "gas" |);
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |)
            ],
            make_dict []
          |);
          M.get_field (| M.get_name (| globals, "extend_memory" |), "cost" |);
          BinOp.add (|
            M.get_name (| globals, "GAS_CALL" |),
            M.get_name (| globals, "transfer_gas_cost" |)
          |)
        ],
        make_dict []
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
    let sender_balance :=
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |)
        ],
        make_dict []
      |), "balance" |) in
    let _ :=
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
    let beneficiary :=
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
      |) in
    let gas_cost :=
      M.get_name (| globals, "GAS_SELF_DESTRUCT" |) in
    let _ :=
        M.pure Constant.None_
      )) |) in
    let originator :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "current_target" |) in
    let refunded_accounts :=
      M.get_field (| M.get_name (| globals, "evm" |), "accounts_to_delete" |) in
    let parent_evm :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "parent_evm" |) in
    While Compare.is_not (|
    M.get_name (| globals, "parent_evm" |),
    Constant.None_
  |) do
      let _ := M.call (|
    M.get_field (| M.get_name (| globals, "refunded_accounts" |), "update" |),
    make_list [
      M.get_field (| M.get_name (| globals, "parent_evm" |), "accounts_to_delete" |)
    ],
    make_dict []
  |) in
      let parent_evm :=
        M.get_field (| M.get_field (| M.get_name (| globals, "parent_evm" |), "message" |), "parent_evm" |) in
    EndWhile.
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
    let beneficiary_balance :=
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "beneficiary" |)
        ],
        make_dict []
      |), "balance" |) in
    let originator_balance :=
      M.get_field (| M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "state" |);
          M.get_name (| globals, "originator" |)
        ],
        make_dict []
      |), "balance" |) in
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
    let _ :=
        M.pure Constant.None_
      )) |) in
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
    let gas :=
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
      |) in
    let code_address :=
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
      |) in
    let memory_input_start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_input_size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_output_start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let memory_output_size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let extend_memory :=
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
      |) in
    let message_call_gas :=
      M.call (|
        M.get_name (| globals, "calculate_message_call_gas" |),
        make_list [
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |);
          M.get_name (| globals, "gas" |);
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |)
            ],
            make_dict []
          |);
          M.get_field (| M.get_name (| globals, "extend_memory" |), "cost" |);
          M.get_name (| globals, "GAS_CALL" |)
        ],
        make_dict []
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
    let _ := M.call (|
    M.get_name (| globals, "generic_call" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_field (| M.get_name (| globals, "message_call_gas" |), "stipend" |);
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
