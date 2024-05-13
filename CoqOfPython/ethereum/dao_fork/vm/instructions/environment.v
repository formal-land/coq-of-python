Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.dao_fork.vm.instructions.environment".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Environmental Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM environment related instructions.
".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_utils_numeric_imports_ceil32 :
  IsImported globals "ethereum.utils.numeric" "ceil32".

Axiom ethereum_dao_fork_state_imports_get_account :
  IsImported globals "ethereum.dao_fork.state" "get_account".

Axiom ethereum_dao_fork_utils_address_imports_to_address :
  IsImported globals "ethereum.dao_fork.utils.address" "to_address".

Axiom ethereum_dao_fork_vm_memory_imports_buffer_read :
  IsImported globals "ethereum.dao_fork.vm.memory" "buffer_read".
Axiom ethereum_dao_fork_vm_memory_imports_memory_write :
  IsImported globals "ethereum.dao_fork.vm.memory" "memory_write".

Axiom ethereum_dao_fork_vm_imports_Evm :
  IsImported globals "ethereum.dao_fork.vm" "Evm".

Axiom ethereum_dao_fork_vm_gas_imports_GAS_BALANCE :
  IsImported globals "ethereum.dao_fork.vm.gas" "GAS_BALANCE".
Axiom ethereum_dao_fork_vm_gas_imports_GAS_BASE :
  IsImported globals "ethereum.dao_fork.vm.gas" "GAS_BASE".
Axiom ethereum_dao_fork_vm_gas_imports_GAS_COPY :
  IsImported globals "ethereum.dao_fork.vm.gas" "GAS_COPY".
Axiom ethereum_dao_fork_vm_gas_imports_GAS_EXTERNAL :
  IsImported globals "ethereum.dao_fork.vm.gas" "GAS_EXTERNAL".
Axiom ethereum_dao_fork_vm_gas_imports_GAS_VERY_LOW :
  IsImported globals "ethereum.dao_fork.vm.gas" "GAS_VERY_LOW".
Axiom ethereum_dao_fork_vm_gas_imports_calculate_gas_extend_memory :
  IsImported globals "ethereum.dao_fork.vm.gas" "calculate_gas_extend_memory".
Axiom ethereum_dao_fork_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.dao_fork.vm.gas" "charge_gas".

Axiom ethereum_dao_fork_vm_stack_imports_pop :
  IsImported globals "ethereum.dao_fork.vm.stack" "pop".
Axiom ethereum_dao_fork_vm_stack_imports_push :
  IsImported globals "ethereum.dao_fork.vm.stack" "push".

Definition address : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Pushes the address of the current executing account to the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BASE" |)
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
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "current_target" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom address_in_globals :
  IsInGlobals globals "address" (make_function address).

Definition balance : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Pushes the balance of the given account onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "address" ,
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
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BALANCE" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "balance" ,
      M.get_field (| M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |), "balance" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "balance" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom balance_in_globals :
  IsInGlobals globals "balance" (make_function balance).

Definition origin : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Pushes the address of the original transaction sender to the stack.
    The origin address can only be an EOA.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BASE" |)
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
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "origin" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom origin_in_globals :
  IsInGlobals globals "origin" (make_function origin).

Definition caller : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Pushes the address of the caller onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BASE" |)
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
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "caller" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom caller_in_globals :
  IsInGlobals globals "caller" (make_function caller).

Definition callvalue : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Push the value (in wei) sent with the call onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BASE" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom callvalue_in_globals :
  IsInGlobals globals "callvalue" (make_function callvalue).

Definition calldataload : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Push a word (32 bytes) of the input data belonging to the current
    environment onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "start_index" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "buffer_read" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |);
          M.get_name (| globals, locals_stack, "start_index" |);
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 32
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "value" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom calldataload_in_globals :
  IsInGlobals globals "calldataload" (make_function calldataload).

Definition calldatasize : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Push the size of input data in current environment onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BASE" |)
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
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom calldatasize_in_globals :
  IsInGlobals globals "calldatasize" (make_function calldatasize).

Definition calldatacopy : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Copy a portion of the input data in current environment to memory.

    This will also expand the memory, in case that the memory is insufficient
    to store the data.

    Parameters
    ----------
    evm :
        The current EVM frame.

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
      "data_start_index" ,
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
      "words" ,
      BinOp.floor_div (|
        M.call (|
          M.get_name (| globals, locals_stack, "ceil32" |),
          make_list [
            M.call (|
              M.get_name (| globals, locals_stack, "Uint" |),
              make_list [
                M.get_name (| globals, locals_stack, "size" |)
              ],
              make_dict []
            |)
          ],
          make_dict []
        |),
        Constant.int 32
      |)
    |) in
    let _ := M.assign_local (|
      "copy_gas_cost" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "GAS_COPY" |),
        M.get_name (| globals, locals_stack, "words" |)
      |)
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
          M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |),
          M.get_name (| globals, locals_stack, "copy_gas_cost" |)
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
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "buffer_read" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |);
          M.get_name (| globals, locals_stack, "data_start_index" |);
          M.get_name (| globals, locals_stack, "size" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "memory_write" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
      M.get_name (| globals, locals_stack, "memory_start_index" |);
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

Axiom calldatacopy_in_globals :
  IsInGlobals globals "calldatacopy" (make_function calldatacopy).

Definition codesize : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Push the size of code running in current environment onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BASE" |)
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
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "code" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom codesize_in_globals :
  IsInGlobals globals "codesize" (make_function codesize).

Definition codecopy : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Copy a portion of the code in current environment to memory.

    This will also expand the memory, in case that the memory is insufficient
    to store the data.

    Parameters
    ----------
    evm :
        The current EVM frame.

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
      "code_start_index" ,
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
      "words" ,
      BinOp.floor_div (|
        M.call (|
          M.get_name (| globals, locals_stack, "ceil32" |),
          make_list [
            M.call (|
              M.get_name (| globals, locals_stack, "Uint" |),
              make_list [
                M.get_name (| globals, locals_stack, "size" |)
              ],
              make_dict []
            |)
          ],
          make_dict []
        |),
        Constant.int 32
      |)
    |) in
    let _ := M.assign_local (|
      "copy_gas_cost" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "GAS_COPY" |),
        M.get_name (| globals, locals_stack, "words" |)
      |)
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
          M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |),
          M.get_name (| globals, locals_stack, "copy_gas_cost" |)
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
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "buffer_read" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "code" |);
          M.get_name (| globals, locals_stack, "code_start_index" |);
          M.get_name (| globals, locals_stack, "size" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "memory_write" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
      M.get_name (| globals, locals_stack, "memory_start_index" |);
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

Axiom codecopy_in_globals :
  IsInGlobals globals "codecopy" (make_function codecopy).

Definition gasprice : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Push the gas price used in current environment onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_BASE" |)
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
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "gas_price" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom gasprice_in_globals :
  IsInGlobals globals "gasprice" (make_function gasprice).

Definition extcodesize : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Push the code size of a given account onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "address" ,
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
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_EXTERNAL" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "codesize" ,
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.call (|
                M.get_name (| globals, locals_stack, "get_account" |),
                make_list [
                  M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
                  M.get_name (| globals, locals_stack, "address" |)
                ],
                make_dict []
              |), "code" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "codesize" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom extcodesize_in_globals :
  IsInGlobals globals "extcodesize" (make_function extcodesize).

Definition extcodecopy : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Copy a portion of an account's code to memory.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "address" ,
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
      "code_start_index" ,
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
      "words" ,
      BinOp.floor_div (|
        M.call (|
          M.get_name (| globals, locals_stack, "ceil32" |),
          make_list [
            M.call (|
              M.get_name (| globals, locals_stack, "Uint" |),
              make_list [
                M.get_name (| globals, locals_stack, "size" |)
              ],
              make_dict []
            |)
          ],
          make_dict []
        |),
        Constant.int 32
      |)
    |) in
    let _ := M.assign_local (|
      "copy_gas_cost" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "GAS_COPY" |),
        M.get_name (| globals, locals_stack, "words" |)
      |)
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
          M.get_name (| globals, locals_stack, "GAS_EXTERNAL" |),
          M.get_name (| globals, locals_stack, "copy_gas_cost" |)
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
      "code" ,
      M.get_field (| M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "env" |), "state" |);
          M.get_name (| globals, locals_stack, "address" |)
        ],
        make_dict []
      |), "code" |)
    |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "buffer_read" |),
        make_list [
          M.get_name (| globals, locals_stack, "code" |);
          M.get_name (| globals, locals_stack, "code_start_index" |);
          M.get_name (| globals, locals_stack, "size" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "memory_write" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
      M.get_name (| globals, locals_stack, "memory_start_index" |);
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

Axiom extcodecopy_in_globals :
  IsInGlobals globals "extcodecopy" (make_function extcodecopy).
