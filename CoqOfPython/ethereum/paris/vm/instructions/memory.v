Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Memory Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM Memory instructions.
".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".

Require ethereum.paris.vm.__init__.
Axiom ethereum_paris_vm___init___Evm :
  IsGlobalAlias globals ethereum.paris.vm.__init__.globals "Evm".

Require ethereum.paris.vm.gas.
Axiom ethereum_paris_vm_gas_GAS_BASE :
  IsGlobalAlias globals ethereum.paris.vm.gas.globals "GAS_BASE".
Axiom ethereum_paris_vm_gas_GAS_VERY_LOW :
  IsGlobalAlias globals ethereum.paris.vm.gas.globals "GAS_VERY_LOW".
Axiom ethereum_paris_vm_gas_calculate_gas_extend_memory :
  IsGlobalAlias globals ethereum.paris.vm.gas.globals "calculate_gas_extend_memory".
Axiom ethereum_paris_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.paris.vm.gas.globals "charge_gas".

Require ethereum.paris.vm.memory.
Axiom ethereum_paris_vm_memory_memory_read_bytes :
  IsGlobalAlias globals ethereum.paris.vm.memory.globals "memory_read_bytes".
Axiom ethereum_paris_vm_memory_memory_write :
  IsGlobalAlias globals ethereum.paris.vm.memory.globals "memory_write".

Require ethereum.paris.vm.stack.
Axiom ethereum_paris_vm_stack_pop :
  IsGlobalAlias globals ethereum.paris.vm.stack.globals "pop".
Axiom ethereum_paris_vm_stack_push :
  IsGlobalAlias globals ethereum.paris.vm.stack.globals "push".

Definition mstore : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Stores a word to memory.
    This also expands the memory, if the memory is
    insufficient to store the word.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let value :=
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
    let extend_memory :=
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "start_position" |); M.call (|
              M.get_name (| globals, "U256" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "len" |),
                  make_list [
                    M.get_name (| globals, "value" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |) ]
          ]
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_name (| globals, "GAS_VERY_LOW" |),
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
    M.get_name (| globals, "memory_write" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
      M.get_name (| globals, "start_position" |);
      M.get_name (| globals, "value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition mstore8 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Stores a byte to memory.
    This also expands the memory, if the memory is
    insufficient to store the word.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let start_position :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
    let extend_memory :=
      M.call (|
        M.get_name (| globals, "calculate_gas_extend_memory" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          make_list [
            make_tuple [ M.get_name (| globals, "start_position" |); M.call (|
              M.get_name (| globals, "U256" |),
              make_list [
                Constant.int 1
              ],
              make_dict []
            |) ]
          ]
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_name (| globals, "GAS_VERY_LOW" |),
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
    let normalized_bytes_value :=
      M.call (|
        M.get_name (| globals, "Bytes" |),
        make_list [
          make_list [
            BinOp.bit_and (|
              M.get_name (| globals, "value" |),
              Constant.int 255
            |)
          ]
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "memory_write" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
      M.get_name (| globals, "start_position" |);
      M.get_name (| globals, "normalized_bytes_value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition mload : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Load word from memory.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let start_position :=
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
            make_tuple [ M.get_name (| globals, "start_position" |); M.call (|
              M.get_name (| globals, "U256" |),
              make_list [
                Constant.int 32
              ],
              make_dict []
            |) ]
          ]
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_name (| globals, "GAS_VERY_LOW" |),
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
    let value :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "memory_read_bytes" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
              M.get_name (| globals, "start_position" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 32
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
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "value" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition msize : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push the size of active memory in bytes onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.pass (| |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_BASE" |)
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
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "memory" |)
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
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).
