Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require typing.
Axiom typing_Iterable :
  IsGlobalAlias globals typing.globals "Iterable".
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
Axiom ethereum_base_types_Bytes0 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes0".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.trace.
Axiom ethereum_trace_EvmStop :
  IsGlobalAlias globals ethereum.trace.globals "EvmStop".
Axiom ethereum_trace_OpEnd :
  IsGlobalAlias globals ethereum.trace.globals "OpEnd".
Axiom ethereum_trace_OpException :
  IsGlobalAlias globals ethereum.trace.globals "OpException".
Axiom ethereum_trace_OpStart :
  IsGlobalAlias globals ethereum.trace.globals "OpStart".
Axiom ethereum_trace_PrecompileEnd :
  IsGlobalAlias globals ethereum.trace.globals "PrecompileEnd".
Axiom ethereum_trace_PrecompileStart :
  IsGlobalAlias globals ethereum.trace.globals "PrecompileStart".
Axiom ethereum_trace_TransactionEnd :
  IsGlobalAlias globals ethereum.trace.globals "TransactionEnd".
Axiom ethereum_trace_evm_trace :
  IsGlobalAlias globals ethereum.trace.globals "evm_trace".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require ethereum.paris.blocks.
Axiom ethereum_paris_blocks_Log :
  IsGlobalAlias globals ethereum.paris.blocks.globals "Log".

Require ethereum.paris.fork_types.
Axiom ethereum_paris_fork_types_Address :
  IsGlobalAlias globals ethereum.paris.fork_types.globals "Address".

Require ethereum.paris.state.
Axiom ethereum_paris_state_account_exists_and_is_empty :
  IsGlobalAlias globals ethereum.paris.state.globals "account_exists_and_is_empty".
Axiom ethereum_paris_state_account_has_code_or_nonce :
  IsGlobalAlias globals ethereum.paris.state.globals "account_has_code_or_nonce".
Axiom ethereum_paris_state_begin_transaction :
  IsGlobalAlias globals ethereum.paris.state.globals "begin_transaction".
Axiom ethereum_paris_state_commit_transaction :
  IsGlobalAlias globals ethereum.paris.state.globals "commit_transaction".
Axiom ethereum_paris_state_destroy_storage :
  IsGlobalAlias globals ethereum.paris.state.globals "destroy_storage".
Axiom ethereum_paris_state_increment_nonce :
  IsGlobalAlias globals ethereum.paris.state.globals "increment_nonce".
Axiom ethereum_paris_state_mark_account_created :
  IsGlobalAlias globals ethereum.paris.state.globals "mark_account_created".
Axiom ethereum_paris_state_move_ether :
  IsGlobalAlias globals ethereum.paris.state.globals "move_ether".
Axiom ethereum_paris_state_rollback_transaction :
  IsGlobalAlias globals ethereum.paris.state.globals "rollback_transaction".
Axiom ethereum_paris_state_set_code :
  IsGlobalAlias globals ethereum.paris.state.globals "set_code".
Axiom ethereum_paris_state_touch_account :
  IsGlobalAlias globals ethereum.paris.state.globals "touch_account".

Require ethereum.paris.vm.__init__.
Axiom ethereum_paris_vm___init___Message :
  IsGlobalAlias globals ethereum.paris.vm.__init__.globals "Message".

Require ethereum.paris.vm.gas.
Axiom ethereum_paris_vm_gas_GAS_CODE_DEPOSIT :
  IsGlobalAlias globals ethereum.paris.vm.gas.globals "GAS_CODE_DEPOSIT".
Axiom ethereum_paris_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.paris.vm.gas.globals "charge_gas".

Require ethereum.paris.vm.precompiled_contracts.mapping.
Axiom ethereum_paris_vm_precompiled_contracts_mapping_PRE_COMPILED_CONTRACTS :
  IsGlobalAlias globals ethereum.paris.vm.precompiled_contracts.mapping.globals "PRE_COMPILED_CONTRACTS".

Require ethereum.paris.vm.__init__.
Axiom ethereum_paris_vm___init___Environment :
  IsGlobalAlias globals ethereum.paris.vm.__init__.globals "Environment".
Axiom ethereum_paris_vm___init___Evm :
  IsGlobalAlias globals ethereum.paris.vm.__init__.globals "Evm".

Require ethereum.paris.vm.exceptions.
Axiom ethereum_paris_vm_exceptions_AddressCollision :
  IsGlobalAlias globals ethereum.paris.vm.exceptions.globals "AddressCollision".
Axiom ethereum_paris_vm_exceptions_ExceptionalHalt :
  IsGlobalAlias globals ethereum.paris.vm.exceptions.globals "ExceptionalHalt".
Axiom ethereum_paris_vm_exceptions_InvalidContractPrefix :
  IsGlobalAlias globals ethereum.paris.vm.exceptions.globals "InvalidContractPrefix".
Axiom ethereum_paris_vm_exceptions_InvalidOpcode :
  IsGlobalAlias globals ethereum.paris.vm.exceptions.globals "InvalidOpcode".
Axiom ethereum_paris_vm_exceptions_OutOfGasError :
  IsGlobalAlias globals ethereum.paris.vm.exceptions.globals "OutOfGasError".
Axiom ethereum_paris_vm_exceptions_Revert :
  IsGlobalAlias globals ethereum.paris.vm.exceptions.globals "Revert".
Axiom ethereum_paris_vm_exceptions_StackDepthLimitError :
  IsGlobalAlias globals ethereum.paris.vm.exceptions.globals "StackDepthLimitError".

Require ethereum.paris.vm.instructions.__init__.
Axiom ethereum_paris_vm_instructions___init___Ops :
  IsGlobalAlias globals ethereum.paris.vm.instructions.__init__.globals "Ops".
Axiom ethereum_paris_vm_instructions___init___op_implementation :
  IsGlobalAlias globals ethereum.paris.vm.instructions.__init__.globals "op_implementation".

Require ethereum.paris.vm.runtime.
Axiom ethereum_paris_vm_runtime_get_valid_jump_destinations :
  IsGlobalAlias globals ethereum.paris.vm.runtime.globals "get_valid_jump_destinations".

Definition STACK_DEPTH_LIMIT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "U256" |),
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
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "message"; "env" ] |) in
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
          M.get_field (| M.get_name (| globals, "message" |), "target" |),
          M.call (|
            M.get_name (| globals, "Bytes0" |),
            make_list [
              Constant.bytes ""
            ],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let is_collision :=
          M.call (|
            M.get_name (| globals, "account_has_code_or_nonce" |),
            make_list [
              M.get_field (| M.get_name (| globals, "env" |), "state" |);
              M.get_field (| M.get_name (| globals, "message" |), "current_target" |)
            ],
            make_dict []
          |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            M.get_name (| globals, "is_collision" |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.call (|
                M.get_name (| globals, "MessageCallOutput" |),
                make_list [
                  M.call (|
                    M.get_name (| globals, "Uint" |),
                    make_list [
                      Constant.int 0
                    ],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, "U256" |),
                    make_list [
                      Constant.int 0
                    ],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, "tuple" |),
                    make_list [],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, "set" |),
                    make_list [],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, "set" |),
                    make_list [],
                    make_dict []
                  |);
                  M.call (|
                    M.get_name (| globals, "AddressCollision" |),
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
            let evm :=
              M.call (|
                M.get_name (| globals, "process_create_message" |),
                make_list [
                  M.get_name (| globals, "message" |);
                  M.get_name (| globals, "env" |)
                ],
                make_dict []
              |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let evm :=
          M.call (|
            M.get_name (| globals, "process_message" |),
            make_list [
              M.get_name (| globals, "message" |);
              M.get_name (| globals, "env" |)
            ],
            make_dict []
          |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, "account_exists_and_is_empty" |),
              make_list [
                M.get_field (| M.get_name (| globals, "env" |), "state" |);
                M.call (|
                  M.get_name (| globals, "Address" |),
                  make_list [
                    M.get_field (| M.get_name (| globals, "message" |), "target" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "touched_accounts" |), "add" |),
    make_list [
      M.call (|
        M.get_name (| globals, "Address" |),
        make_list [
          M.get_field (| M.get_name (| globals, "message" |), "target" |)
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
        M.get_field (| M.get_name (| globals, "evm" |), "error" |),
      (* then *)
      ltac:(M.monadic (
(* At stmt: unsupported node type: AnnAssign *)
        let accounts_to_delete :=
          M.call (|
            M.get_name (| globals, "set" |),
            make_list [],
            make_dict []
          |) in
        let touched_accounts :=
          M.call (|
            M.get_name (| globals, "set" |),
            make_list [],
            make_dict []
          |) in
        let refund_counter :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let logs :=
          M.get_field (| M.get_name (| globals, "evm" |), "logs" |) in
        let accounts_to_delete :=
          M.get_field (| M.get_name (| globals, "evm" |), "accounts_to_delete" |) in
        let touched_accounts :=
          M.get_field (| M.get_name (| globals, "evm" |), "touched_accounts" |) in
        let refund_counter :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "refund_counter" |)
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      )) |) in
    let tx_end :=
      M.call (|
        M.get_name (| globals, "TransactionEnd" |),
        make_list [
          BinOp.sub (|
            M.get_field (| M.get_name (| globals, "message" |), "gas" |),
            M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |)
          |);
          M.get_field (| M.get_name (| globals, "evm" |), "output" |);
          M.get_field (| M.get_name (| globals, "evm" |), "error" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "evm_trace" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "tx_end" |)
    ],
    make_dict []
  |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "MessageCallOutput" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition process_create_message : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "message"; "env" ] |) in
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
    evm: :py:class:`~ethereum.paris.vm.Evm`
        Items containing execution specific objects.
    " in
    let _ := M.call (|
    M.get_name (| globals, "begin_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "destroy_storage" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, "message" |), "current_target" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "mark_account_created" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, "message" |), "current_target" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, "message" |), "current_target" |)
    ],
    make_dict []
  |) in
    let evm :=
      M.call (|
        M.get_name (| globals, "process_message" |),
        make_list [
          M.get_name (| globals, "message" |);
          M.get_name (| globals, "env" |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        UnOp.not (| M.get_field (| M.get_name (| globals, "evm" |), "error" |) |),
      (* then *)
      ltac:(M.monadic (
        let contract_code :=
          M.get_field (| M.get_name (| globals, "evm" |), "output" |) in
        let contract_code_gas :=
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, "len" |),
              make_list [
                M.get_name (| globals, "contract_code" |)
              ],
              make_dict []
            |),
            M.get_name (| globals, "GAS_CODE_DEPOSIT" |)
          |) in
(* At stmt: unsupported node type: Try *)
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "rollback_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.get_name (| globals, "evm" |)
    |) in
    M.pure Constant.None_)).

Definition process_message : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "message"; "env" ] |) in
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
    evm: :py:class:`~ethereum.paris.vm.Evm`
        Items containing execution specific objects
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.get_field (| M.get_name (| globals, "message" |), "depth" |),
          M.get_name (| globals, "STACK_DEPTH_LIMIT" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some(M.call (|
          M.get_name (| globals, "StackDepthLimitError" |),
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
    M.get_name (| globals, "begin_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "touch_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, "message" |), "current_target" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          M.get_field (| M.get_name (| globals, "message" |), "should_transfer_value" |),
          ltac:(M.monadic (
            Compare.not_eq (|
              M.get_field (| M.get_name (| globals, "message" |), "value" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "move_ether" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, "message" |), "caller" |);
      M.get_field (| M.get_name (| globals, "message" |), "current_target" |);
      M.get_field (| M.get_name (| globals, "message" |), "value" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let evm :=
      M.call (|
        M.get_name (| globals, "execute_code" |),
        make_list [
          M.get_name (| globals, "message" |);
          M.get_name (| globals, "env" |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.get_field (| M.get_name (| globals, "evm" |), "error" |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "rollback_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "commit_transaction" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.get_name (| globals, "evm" |)
    |) in
    M.pure Constant.None_)).

Definition execute_code : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "message"; "env" ] |) in
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
    let code :=
      M.get_field (| M.get_name (| globals, "message" |), "code" |) in
    let valid_jump_destinations :=
      M.call (|
        M.get_name (| globals, "get_valid_jump_destinations" |),
        make_list [
          M.get_name (| globals, "code" |)
        ],
        make_dict []
      |) in
    let evm :=
      M.call (|
        M.get_name (| globals, "Evm" |),
        make_list [],
        make_dict []
      |) in
(* At stmt: unsupported node type: Try *)
    let _ := M.return_ (|
      M.get_name (| globals, "evm" |)
    |) in
    M.pure Constant.None_)).