Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Logging Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM logging instructions.
".

Require functools.
Axiom functools_partial :
  IsGlobalAlias globals functools.globals "partial".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".

Require ethereum.tangerine_whistle.blocks.
Axiom ethereum_tangerine_whistle_blocks_Log :
  IsGlobalAlias globals ethereum.tangerine_whistle.blocks.globals "Log".

Require ethereum.tangerine_whistle.vm.__init__.
Axiom ethereum_tangerine_whistle_vm___init___Evm :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.__init__.globals "Evm".

Require ethereum.tangerine_whistle.vm.gas.
Axiom ethereum_tangerine_whistle_vm_gas_GAS_LOG :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.gas.globals "GAS_LOG".
Axiom ethereum_tangerine_whistle_vm_gas_GAS_LOG_DATA :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.gas.globals "GAS_LOG_DATA".
Axiom ethereum_tangerine_whistle_vm_gas_GAS_LOG_TOPIC :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.gas.globals "GAS_LOG_TOPIC".
Axiom ethereum_tangerine_whistle_vm_gas_calculate_gas_extend_memory :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.gas.globals "calculate_gas_extend_memory".
Axiom ethereum_tangerine_whistle_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.gas.globals "charge_gas".

Require ethereum.tangerine_whistle.vm.memory.
Axiom ethereum_tangerine_whistle_vm_memory_memory_read_bytes :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.memory.globals "memory_read_bytes".

Require ethereum.tangerine_whistle.vm.stack.
Axiom ethereum_tangerine_whistle_vm_stack_pop :
  IsGlobalAlias globals ethereum.tangerine_whistle.vm.stack.globals "pop".

Definition log_n : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "num_topics" ] |) in
    let _ := Constant.str "
    Appends a log entry, having `num_topics` topics, to the evm logs.

    This will also expand the memory if the data (required by the log entry)
    corresponding to the memory is not accessible.

    Parameters
    ----------
    evm :
        The current EVM frame.
    num_topics :
        The number of topics to be included in the log entry.

    " in
    let memory_start_index :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let size :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let topics :=
      make_list [] in
    For M.get_name (| globals, "_" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      M.get_name (| globals, "num_topics" |)
    ],
    make_dict []
  |) do
      let topic :=
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
    M.get_field (| M.get_name (| globals, "topics" |), "append" |),
    make_list [
      M.get_name (| globals, "topic" |)
    ],
    make_dict []
  |) in
    EndFor.
    let extend_memory :=
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_start_index" |); M.get_name (| globals, "size" |) ]
          ]
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        BinOp.add (|
          BinOp.add (|
            M.get_name (| globals, "GAS_LOG" |),
            BinOp.mult (|
              M.get_name (| globals, "GAS_LOG_DATA" |),
              M.get_name (| globals, "size" |)
            |)
          |),
          BinOp.mult (|
            M.get_name (| globals, "GAS_LOG_TOPIC" |),
            M.get_name (| globals, "num_topics" |)
          |)
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
    let log_entry :=
      M.call (|
        M.get_name (| globals, "Log" |),
        make_list [],
        make_dict []
      |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "logs" |),
      BinOp.add (|
        M.get_field (| M.get_name (| globals, "evm" |), "logs" |),
        make_tuple [ M.get_name (| globals, "log_entry" |) ]
      |)
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition log0 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "log_n" |)
    ],
    make_dict []
  |)
)).

Definition log1 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "log_n" |)
    ],
    make_dict []
  |)
)).

Definition log2 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "log_n" |)
    ],
    make_dict []
  |)
)).

Definition log3 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "log_n" |)
    ],
    make_dict []
  |)
)).

Definition log4 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "partial" |),
    make_list [
      M.get_name (| globals, "log_n" |)
    ],
    make_dict []
  |)
)).