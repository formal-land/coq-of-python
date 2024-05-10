Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.gray_glacier.vm.instructions.log".

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

Axiom functools_imports_partial :
  IsImported globals "functools" "partial".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".

Axiom ethereum_utils_ensure_imports_ensure :
  IsImported globals "ethereum.utils.ensure" "ensure".

Axiom ethereum_gray_glacier_blocks_imports_Log :
  IsImported globals "ethereum.gray_glacier.blocks" "Log".

Axiom ethereum_gray_glacier_vm_imports_Evm :
  IsImported globals "ethereum.gray_glacier.vm" "Evm".

Axiom ethereum_gray_glacier_vm_exceptions_imports_WriteInStaticContext :
  IsImported globals "ethereum.gray_glacier.vm.exceptions" "WriteInStaticContext".

Axiom ethereum_gray_glacier_vm_gas_imports_GAS_LOG :
  IsImported globals "ethereum.gray_glacier.vm.gas" "GAS_LOG".
Axiom ethereum_gray_glacier_vm_gas_imports_GAS_LOG_DATA :
  IsImported globals "ethereum.gray_glacier.vm.gas" "GAS_LOG_DATA".
Axiom ethereum_gray_glacier_vm_gas_imports_GAS_LOG_TOPIC :
  IsImported globals "ethereum.gray_glacier.vm.gas" "GAS_LOG_TOPIC".
Axiom ethereum_gray_glacier_vm_gas_imports_calculate_gas_extend_memory :
  IsImported globals "ethereum.gray_glacier.vm.gas" "calculate_gas_extend_memory".
Axiom ethereum_gray_glacier_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.gray_glacier.vm.gas" "charge_gas".

Axiom ethereum_gray_glacier_vm_memory_imports_memory_read_bytes :
  IsImported globals "ethereum.gray_glacier.vm.memory" "memory_read_bytes".

Axiom ethereum_gray_glacier_vm_stack_imports_pop :
  IsImported globals "ethereum.gray_glacier.vm.stack" "pop".

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
    let _ := M.assign_local (|
      "memory_start_index" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "size" ,
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "topics" ,
      make_list []
    |) in
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
          let _ := M.assign_local (|
            "topic" ,
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
    let _ := M.assign_local (|
      "extend_memory" ,
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "memory_start_index" |); M.get_name (| globals, "size" |) ]
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
    let _ := M.assign_local (|
      "log_entry" ,
      M.call (|
        M.get_name (| globals, "Log" |),
        make_list [],
        make_dict []
      |)
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
