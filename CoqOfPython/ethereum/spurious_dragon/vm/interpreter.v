Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.spurious_dragon.vm.interpreter".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Interpreter
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

A straightforward interpreter that executes EVM code.
".

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_Iterable :
  IsImported globals "typing" "Iterable".
Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Set :
  IsImported globals "typing" "Set".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_trace_imports_EvmStop :
  IsImported globals "ethereum.trace" "EvmStop".
Axiom ethereum_trace_imports_OpEnd :
  IsImported globals "ethereum.trace" "OpEnd".
Axiom ethereum_trace_imports_OpException :
  IsImported globals "ethereum.trace" "OpException".
Axiom ethereum_trace_imports_OpStart :
  IsImported globals "ethereum.trace" "OpStart".
Axiom ethereum_trace_imports_PrecompileEnd :
  IsImported globals "ethereum.trace" "PrecompileEnd".
Axiom ethereum_trace_imports_PrecompileStart :
  IsImported globals "ethereum.trace" "PrecompileStart".
Axiom ethereum_trace_imports_TransactionEnd :
  IsImported globals "ethereum.trace" "TransactionEnd".
Axiom ethereum_trace_imports_evm_trace :
  IsImported globals "ethereum.trace" "evm_trace".

Axiom ethereum_utils_ensure_imports_ensure :
  IsImported globals "ethereum.utils.ensure" "ensure".

Axiom ethereum_spurious_dragon_blocks_imports_Log :
  IsImported globals "ethereum.spurious_dragon.blocks" "Log".

Axiom ethereum_spurious_dragon_fork_types_imports_Address :
  IsImported globals "ethereum.spurious_dragon.fork_types" "Address".

Axiom ethereum_spurious_dragon_state_imports_account_exists_and_is_empty :
  IsImported globals "ethereum.spurious_dragon.state" "account_exists_and_is_empty".
Axiom ethereum_spurious_dragon_state_imports_account_has_code_or_nonce :
  IsImported globals "ethereum.spurious_dragon.state" "account_has_code_or_nonce".
Axiom ethereum_spurious_dragon_state_imports_begin_transaction :
  IsImported globals "ethereum.spurious_dragon.state" "begin_transaction".
Axiom ethereum_spurious_dragon_state_imports_commit_transaction :
  IsImported globals "ethereum.spurious_dragon.state" "commit_transaction".
Axiom ethereum_spurious_dragon_state_imports_destroy_storage :
  IsImported globals "ethereum.spurious_dragon.state" "destroy_storage".
Axiom ethereum_spurious_dragon_state_imports_increment_nonce :
  IsImported globals "ethereum.spurious_dragon.state" "increment_nonce".
Axiom ethereum_spurious_dragon_state_imports_move_ether :
  IsImported globals "ethereum.spurious_dragon.state" "move_ether".
Axiom ethereum_spurious_dragon_state_imports_rollback_transaction :
  IsImported globals "ethereum.spurious_dragon.state" "rollback_transaction".
Axiom ethereum_spurious_dragon_state_imports_set_code :
  IsImported globals "ethereum.spurious_dragon.state" "set_code".
Axiom ethereum_spurious_dragon_state_imports_touch_account :
  IsImported globals "ethereum.spurious_dragon.state" "touch_account".

Axiom ethereum_spurious_dragon_vm_imports_Message :
  IsImported globals "ethereum.spurious_dragon.vm" "Message".

Axiom ethereum_spurious_dragon_vm_gas_imports_GAS_CODE_DEPOSIT :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "GAS_CODE_DEPOSIT".
Axiom ethereum_spurious_dragon_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.spurious_dragon.vm.gas" "charge_gas".

Axiom ethereum_spurious_dragon_vm_precompiled_contracts_mapping_imports_PRE_COMPILED_CONTRACTS :
  IsImported globals "ethereum.spurious_dragon.vm.precompiled_contracts.mapping" "PRE_COMPILED_CONTRACTS".

Axiom ethereum_spurious_dragon_vm_imports_Environment :
  IsImported globals "ethereum.spurious_dragon.vm" "Environment".
Axiom ethereum_spurious_dragon_vm_imports_Evm :
  IsImported globals "ethereum.spurious_dragon.vm" "Evm".

Axiom ethereum_spurious_dragon_vm_exceptions_imports_AddressCollision :
  IsImported globals "ethereum.spurious_dragon.vm.exceptions" "AddressCollision".
Axiom ethereum_spurious_dragon_vm_exceptions_imports_ExceptionalHalt :
  IsImported globals "ethereum.spurious_dragon.vm.exceptions" "ExceptionalHalt".
Axiom ethereum_spurious_dragon_vm_exceptions_imports_InvalidOpcode :
  IsImported globals "ethereum.spurious_dragon.vm.exceptions" "InvalidOpcode".
Axiom ethereum_spurious_dragon_vm_exceptions_imports_OutOfGasError :
  IsImported globals "ethereum.spurious_dragon.vm.exceptions" "OutOfGasError".
Axiom ethereum_spurious_dragon_vm_exceptions_imports_StackDepthLimitError :
  IsImported globals "ethereum.spurious_dragon.vm.exceptions" "StackDepthLimitError".

Axiom ethereum_spurious_dragon_vm_instructions_imports_Ops :
  IsImported globals "ethereum.spurious_dragon.vm.instructions" "Ops".
Axiom ethereum_spurious_dragon_vm_instructions_imports_op_implementation :
  IsImported globals "ethereum.spurious_dragon.vm.instructions" "op_implementation".

Axiom ethereum_spurious_dragon_vm_runtime_imports_get_valid_jump_destinations :
  IsImported globals "ethereum.spurious_dragon.vm.runtime" "get_valid_jump_destinations".

Definition STACK_DEPTH_LIMIT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "U256" |),
    make_list [
      Constant.int 1024
    ],
    make_dict []
  |)
)).

Definition MAX_CODE_SIZE : Value.t := M.run ltac:(M.monadic (
  Constant.int 24576
)).

Definition MessageCallOutput : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition process_message_call : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "message"; "env" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    If `message.current` is empty then it creates a smart contract
    else it executes a call from the `message.caller` to the `message.target`.

    Parameters
    ----------
    message :
        Transaction specific items.

    env :
        External items required for EVM execution.

    Returns
    -------
    output : `MessageCallOutput`
        Output of the message call
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "message" |), "target" |),
          M.call (|
            M.get_name (| globals, locals_stack, "Bytes0" |),
            make_list [
              Constant.bytes ""
            ],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "is_collision" ,
          M.call (|
            M.get_name (| globals, locals_stack, "account_has_code_or_nonce" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
              M.get_field (| M.get_name (| globals, locals_stack, "message" |), "current_target" |)
            ],
            make_dict []
          |)
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            M.get_name (| globals, locals_stack, "is_collision" |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.call (|
                M.get_name (| globals, locals_stack, "MessageCallOutput" |),
                make_list [
                  M.call (|
                    M.get_name (| globals, locals_stack, "Uint" |),
                    make_list [
                      Constant.int 0
                    ],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "U256" |),
                    make_list [
                      Constant.int 0
                    ],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "tuple" |),
                    make_list [],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "set" |),
                    make_list [],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "set" |),
                    make_list [],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "AddressCollision" |),
                    make_list [],
                    make_dict []
                  |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "evm" ,
              M.call (|
                M.get_name (| globals, locals_stack, "process_create_message" |),
                make_list [
                  M.get_name (| globals, locals_stack, "message" |);
                  M.get_name (| globals, locals_stack, "env" |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "evm" ,
          M.call (|
            M.get_name (| globals, locals_stack, "process_message" |),
            make_list [
              M.get_name (| globals, locals_stack, "message" |);
              M.get_name (| globals, locals_stack, "env" |)
            ],
            make_dict []
          |)
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, locals_stack, "account_exists_and_is_empty" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
                M.call (|
                  M.get_name (| globals, locals_stack, "Address" |),
                  make_list [
                    M.get_field (| M.get_name (| globals, locals_stack, "message" |), "target" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "touched_accounts" |), "add" |),
    make_list [
      M.call (|
        M.get_name (| globals, locals_stack, "Address" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "message" |), "target" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "error" |),
      (* then *)
      ltac:(M.monadic (
(* At stmt: unsupported node type: AnnAssign *)
        let _ := M.assign_local (|
          "accounts_to_delete" ,
          M.call (|
            M.get_name (| globals, locals_stack, "set" |),
            make_list [],
            make_dict []
          |)
        |) in
        let _ := M.assign_local (|
          "touched_accounts" ,
          M.call (|
            M.get_name (| globals, locals_stack, "set" |),
            make_list [],
            make_dict []
          |)
        |) in
        let _ := M.assign_local (|
          "refund_counter" ,
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "logs" ,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "logs" |)
        |) in
        let _ := M.assign_local (|
          "accounts_to_delete" ,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "accounts_to_delete" |)
        |) in
        let _ := M.assign_local (|
          "touched_accounts" ,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "touched_accounts" |)
        |) in
        let _ := M.assign_local (|
          "refund_counter" ,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "refund_counter" |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "tx_end" ,
      M.call (|
        M.get_name (| globals, locals_stack, "TransactionEnd" |),
        make_list [
          BinOp.sub (|
            M.get_field (| M.get_name (| globals, locals_stack, "message" |), "gas" |),
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |)
          |);
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |);
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "error" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "evm_trace" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "tx_end" |)
    ],
    make_dict []
  |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "MessageCallOutput" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition process_create_message : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "message"; "env" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Executes a call to create a smart contract.

    Parameters
    ----------
    message :
        Transaction specific items.
    env :
        External items required for EVM execution.

    Returns
    -------
    evm: :py:class:`~ethereum.spurious_dragon.vm.Evm`
        Items containing execution specific objects.
    " in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "begin_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "destroy_storage" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message" |), "current_target" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message" |), "current_target" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "evm" ,
      M.call (|
        M.get_name (| globals, locals_stack, "process_message" |),
        make_list [
          M.get_name (| globals, locals_stack, "message" |);
          M.get_name (| globals, locals_stack, "env" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        UnOp.not (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "error" |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "contract_code" ,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |)
        |) in
        let _ := M.assign_local (|
          "contract_code_gas" ,
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                M.get_name (| globals, locals_stack, "contract_code" |)
              ],
              make_dict []
            |),
            M.get_name (| globals, locals_stack, "GAS_CODE_DEPOSIT" |)
          |)
        |) in
(* At stmt: unsupported node type: Try *)
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "rollback_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "evm" |)
    |) in
    M.pure Constant.None_)).

Definition process_message : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "message"; "env" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Executes a call to create a smart contract.

    Parameters
    ----------
    message :
        Transaction specific items.
    env :
        External items required for EVM execution.

    Returns
    -------
    evm: :py:class:`~ethereum.spurious_dragon.vm.Evm`
        Items containing execution specific objects
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.get_field (| M.get_name (| globals, locals_stack, "message" |), "depth" |),
          M.get_name (| globals, locals_stack, "STACK_DEPTH_LIMIT" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.call (|
          M.get_name (| globals, locals_stack, "StackDepthLimitError" |),
          make_list [
            Constant.str "Stack depth limit reached"
          ],
          make_dict []
        |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "begin_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "touch_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message" |), "current_target" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          M.get_field (| M.get_name (| globals, locals_stack, "message" |), "should_transfer_value" |),
          ltac:(M.monadic (
            Compare.not_eq (|
              M.get_field (| M.get_name (| globals, locals_stack, "message" |), "value" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "move_ether" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message" |), "caller" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message" |), "current_target" |);
      M.get_field (| M.get_name (| globals, locals_stack, "message" |), "value" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "evm" ,
      M.call (|
        M.get_name (| globals, locals_stack, "execute_code" |),
        make_list [
          M.get_name (| globals, locals_stack, "message" |);
          M.get_name (| globals, locals_stack, "env" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "error" |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "rollback_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "commit_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "evm" |)
    |) in
    M.pure Constant.None_)).

Definition execute_code : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "message"; "env" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Executes bytecode present in the `message`.

    Parameters
    ----------
    message :
        Transaction specific items.
    env :
        External items required for EVM execution.

    Returns
    -------
    evm: `ethereum.vm.EVM`
        Items containing execution specific objects
    " in
    let _ := M.assign_local (|
      "code" ,
      M.get_field (| M.get_name (| globals, locals_stack, "message" |), "code" |)
    |) in
    let _ := M.assign_local (|
      "valid_jump_destinations" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_valid_jump_destinations" |),
        make_list [
          M.get_name (| globals, locals_stack, "code" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "evm" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Evm" |),
        make_list [],
        make_dict []
      |)
    |) in
(* At stmt: unsupported node type: Try *)
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "evm" |)
    |) in
    M.pure Constant.None_)).
