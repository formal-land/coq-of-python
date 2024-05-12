Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.homestead.vm.instructions.log".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_homestead_blocks_imports_Log :
  IsImported globals "ethereum.homestead.blocks" "Log".

Axiom ethereum_homestead_vm_imports_Evm :
  IsImported globals "ethereum.homestead.vm" "Evm".

Axiom ethereum_homestead_vm_gas_imports_GAS_LOG :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_LOG".
Axiom ethereum_homestead_vm_gas_imports_GAS_LOG_DATA :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_LOG_DATA".
Axiom ethereum_homestead_vm_gas_imports_GAS_LOG_TOPIC :
  IsImported globals "ethereum.homestead.vm.gas" "GAS_LOG_TOPIC".
Axiom ethereum_homestead_vm_gas_imports_calculate_gas_extend_memory :
  IsImported globals "ethereum.homestead.vm.gas" "calculate_gas_extend_memory".
Axiom ethereum_homestead_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.homestead.vm.gas" "charge_gas".

Axiom ethereum_homestead_vm_memory_imports_memory_read_bytes :
  IsImported globals "ethereum.homestead.vm.memory" "memory_read_bytes".

Axiom ethereum_homestead_vm_stack_imports_pop :
  IsImported globals "ethereum.homestead.vm.stack" "pop".

Definition log_n : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm"; "num_topics" ] in
    ltac:(M.monadic (
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
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
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
        M.get_name (| globals, locals_stack, "_" |),
        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.get_name (| globals, locals_stack, "num_topics" |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "topic" ,
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
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "topics" |), "append" |),
    make_list [
      M.get_name (| globals, locals_stack, "topic" |)
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
        M.get_name (| globals, locals_stack, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, locals_stack, "memory_start_index" |); M.get_name (| globals, locals_stack, "size" |) ]
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
        BinOp.add (|
          BinOp.add (|
            M.get_name (| globals, locals_stack, "GAS_LOG" |),
            BinOp.mult (|
              M.get_name (| globals, locals_stack, "GAS_LOG_DATA" |),
              M.get_name (| globals, locals_stack, "size" |)
            |)
          |),
          BinOp.mult (|
            M.get_name (| globals, locals_stack, "GAS_LOG_TOPIC" |),
            M.get_name (| globals, locals_stack, "num_topics" |)
          |)
        |),
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
      "log_entry" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Log" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "logs" |),
      BinOp.add (|
        M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "logs" |),
        make_tuple [ M.get_name (| globals, locals_stack, "log_entry" |) ]
      |)
    |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition log0 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "log_n" |)
    ],
    make_dict []
  |)
)).

Definition log1 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "log_n" |)
    ],
    make_dict []
  |)
)).

Definition log2 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "log_n" |)
    ],
    make_dict []
  |)
)).

Definition log3 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "log_n" |)
    ],
    make_dict []
  |)
)).

Definition log4 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "partial" |),
    make_list [
      M.get_name (| globals, locals_stack, "log_n" |)
    ],
    make_dict []
  |)
)).
