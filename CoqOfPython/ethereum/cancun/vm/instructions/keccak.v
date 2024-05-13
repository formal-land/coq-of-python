Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.cancun.vm.instructions.keccak".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_crypto_hash_imports_keccak256 :
  IsImported globals "ethereum.crypto.hash" "keccak256".

Axiom ethereum_utils_numeric_imports_ceil32 :
  IsImported globals "ethereum.utils.numeric" "ceil32".

Axiom ethereum_cancun_vm_imports_Evm :
  IsImported globals "ethereum.cancun.vm" "Evm".

Axiom ethereum_cancun_vm_gas_imports_GAS_KECCAK256 :
  IsImported globals "ethereum.cancun.vm.gas" "GAS_KECCAK256".
Axiom ethereum_cancun_vm_gas_imports_GAS_KECCAK256_WORD :
  IsImported globals "ethereum.cancun.vm.gas" "GAS_KECCAK256_WORD".
Axiom ethereum_cancun_vm_gas_imports_calculate_gas_extend_memory :
  IsImported globals "ethereum.cancun.vm.gas" "calculate_gas_extend_memory".
Axiom ethereum_cancun_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.cancun.vm.gas" "charge_gas".

Axiom ethereum_cancun_vm_memory_imports_memory_read_bytes :
  IsImported globals "ethereum.cancun.vm.memory" "memory_read_bytes".

Axiom ethereum_cancun_vm_stack_imports_pop :
  IsImported globals "ethereum.cancun.vm.stack" "pop".
Axiom ethereum_cancun_vm_stack_imports_push :
  IsImported globals "ethereum.cancun.vm.stack" "push".

Definition keccak : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Pushes to the stack the Keccak-256 hash of a region of memory.

    This also expands the memory, in case the memory is insufficient to
    access the data's memory location.

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
      "word_gas_cost" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "GAS_KECCAK256_WORD" |),
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
          M.get_name (| globals, locals_stack, "GAS_KECCAK256" |),
          M.get_name (| globals, locals_stack, "word_gas_cost" |)
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
      "data" ,
      M.call (|
        M.get_name (| globals, locals_stack, "memory_read_bytes" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "memory" |);
          M.get_name (| globals, locals_stack, "memory_start_index" |);
          M.get_name (| globals, locals_stack, "size" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "hash" ,
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.get_name (| globals, locals_stack, "data" |)
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
          M.get_name (| globals, locals_stack, "hash" |)
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

Axiom keccak_in_globals :
  IsInGlobals globals "keccak" (make_function keccak).
