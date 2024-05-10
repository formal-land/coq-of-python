Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Keccak Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM keccak instructions.
".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_keccak256 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak256".

Require ethereum.utils.numeric.
Axiom ethereum_utils_numeric_ceil32 :
  IsGlobalAlias globals ethereum.utils.numeric.globals "ceil32".

Require ethereum.dao_fork.vm.__init__.
Axiom ethereum_dao_fork_vm___init___Evm :
  IsGlobalAlias globals ethereum.dao_fork.vm.__init__.globals "Evm".

Require ethereum.dao_fork.vm.gas.
Axiom ethereum_dao_fork_vm_gas_GAS_KECCAK256 :
  IsGlobalAlias globals ethereum.dao_fork.vm.gas.globals "GAS_KECCAK256".
Axiom ethereum_dao_fork_vm_gas_GAS_KECCAK256_WORD :
  IsGlobalAlias globals ethereum.dao_fork.vm.gas.globals "GAS_KECCAK256_WORD".
Axiom ethereum_dao_fork_vm_gas_calculate_gas_extend_memory :
  IsGlobalAlias globals ethereum.dao_fork.vm.gas.globals "calculate_gas_extend_memory".
Axiom ethereum_dao_fork_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.dao_fork.vm.gas.globals "charge_gas".

Require ethereum.dao_fork.vm.memory.
Axiom ethereum_dao_fork_vm_memory_memory_read_bytes :
  IsGlobalAlias globals ethereum.dao_fork.vm.memory.globals "memory_read_bytes".

Require ethereum.dao_fork.vm.stack.
Axiom ethereum_dao_fork_vm_stack_pop :
  IsGlobalAlias globals ethereum.dao_fork.vm.stack.globals "pop".
Axiom ethereum_dao_fork_vm_stack_push :
  IsGlobalAlias globals ethereum.dao_fork.vm.stack.globals "push".

Definition keccak : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Pushes to the stack the Keccak-256 hash of a region of memory.

    This also expands the memory, in case the memory is insufficient to
    access the data's memory location.

    Parameters
    ----------
    evm :
        The current EVM frame.

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
    let words :=
      BinOp.floor_div (|
        M.call (|
          M.get_name (| globals, "ceil32" |),
          make_list [
            M.call (|
              M.get_name (| globals, "Uint" |),
              make_list [
                M.get_name (| globals, "size" |)
              ],
              make_dict []
            |)
          ],
          make_dict []
        |),
        Constant.int 32
      |) in
    let word_gas_cost :=
      BinOp.mult (|
        M.get_name (| globals, "GAS_KECCAK256_WORD" |),
        M.get_name (| globals, "words" |)
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
          M.get_name (| globals, "GAS_KECCAK256" |),
          M.get_name (| globals, "word_gas_cost" |)
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
    let data :=
      M.call (|
        M.get_name (| globals, "memory_read_bytes" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "memory" |);
          M.get_name (| globals, "memory_start_index" |);
          M.get_name (| globals, "size" |)
        ],
        make_dict []
      |) in
    let hash :=
      M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.get_name (| globals, "data" |)
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
          M.get_name (| globals, "hash" |)
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
