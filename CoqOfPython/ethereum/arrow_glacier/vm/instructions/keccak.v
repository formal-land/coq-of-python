Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.arrow_glacier.vm.instructions.keccak".

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

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U256"; "Uint" ].

Axiom ethereum_crypto_hash_imports :
  AreImported globals "ethereum.crypto.hash" [ "keccak256" ].

Axiom ethereum_utils_numeric_imports :
  AreImported globals "ethereum.utils.numeric" [ "ceil32" ].

Axiom ethereum_arrow_glacier_vm_imports :
  AreImported globals "ethereum.arrow_glacier.vm" [ "Evm" ].

Axiom ethereum_arrow_glacier_vm_gas_imports :
  AreImported globals "ethereum.arrow_glacier.vm.gas" [ "GAS_KECCAK256"; "GAS_KECCAK256_WORD"; "calculate_gas_extend_memory"; "charge_gas" ].

Axiom ethereum_arrow_glacier_vm_memory_imports :
  AreImported globals "ethereum.arrow_glacier.vm.memory" [ "memory_read_bytes" ].

Axiom ethereum_arrow_glacier_vm_stack_imports :
  AreImported globals "ethereum.arrow_glacier.vm.stack" [ "pop"; "push" ].

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
