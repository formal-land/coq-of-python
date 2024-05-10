Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.istanbul.vm.instructions.log".

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

Axiom functools_imports :
  AreImported globals "functools" [ "partial" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U256" ].

Axiom ethereum_utils_ensure_imports :
  AreImported globals "ethereum.utils.ensure" [ "ensure" ].

Axiom ethereum_istanbul_blocks_imports :
  AreImported globals "ethereum.istanbul.blocks" [ "Log" ].

Axiom ethereum_istanbul_vm_imports :
  AreImported globals "ethereum.istanbul.vm" [ "Evm" ].

Axiom ethereum_istanbul_vm_exceptions_imports :
  AreImported globals "ethereum.istanbul.vm.exceptions" [ "WriteInStaticContext" ].

Axiom ethereum_istanbul_vm_gas_imports :
  AreImported globals "ethereum.istanbul.vm.gas" [ "GAS_LOG"; "GAS_LOG_DATA"; "GAS_LOG_TOPIC"; "calculate_gas_extend_memory"; "charge_gas" ].

Axiom ethereum_istanbul_vm_memory_imports :
  AreImported globals "ethereum.istanbul.vm.memory" [ "memory_read_bytes" ].

Axiom ethereum_istanbul_vm_stack_imports :
  AreImported globals "ethereum.istanbul.vm.stack" [ "pop" ].

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
    let _ :=
      M.for_ (|
        M.get_name (| globals, "_" |),
        M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        M.get_name (| globals, "num_topics" |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
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
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
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
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      UnOp.not (| M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "is_static" |) |);
      M.get_name (| globals, "WriteInStaticContext" |)
    ],
    make_dict []
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
