Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Block Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM block instructions.
".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".

Require ethereum.byzantium.vm.__init__.
Axiom ethereum_byzantium_vm___init___Evm :
  IsGlobalAlias globals ethereum.byzantium.vm.__init__.globals "Evm".

Require ethereum.byzantium.vm.gas.
Axiom ethereum_byzantium_vm_gas_GAS_BASE :
  IsGlobalAlias globals ethereum.byzantium.vm.gas.globals "GAS_BASE".
Axiom ethereum_byzantium_vm_gas_GAS_BLOCK_HASH :
  IsGlobalAlias globals ethereum.byzantium.vm.gas.globals "GAS_BLOCK_HASH".
Axiom ethereum_byzantium_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.byzantium.vm.gas.globals "charge_gas".

Require ethereum.byzantium.vm.stack.
Axiom ethereum_byzantium_vm_stack_pop :
  IsGlobalAlias globals ethereum.byzantium.vm.stack.globals "pop".
Axiom ethereum_byzantium_vm_stack_push :
  IsGlobalAlias globals ethereum.byzantium.vm.stack.globals "push".

Definition block_hash : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push the hash of one of the 256 most recent complete blocks onto the
    stack. The block number to hash is present at the top of the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let block_number :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_BLOCK_HASH" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.lt_e (|
            M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "number" |),
            M.get_name (| globals, "block_number" |)
          |),
          ltac:(M.monadic (
            Compare.gt (|
              M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "number" |),
              BinOp.add (|
                M.get_name (| globals, "block_number" |),
                Constant.int 256
              |)
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let hash :=
          Constant.bytes "00" in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let hash :=
          M.get_subscript (| M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "block_hashes" |), UnOp.sub (| BinOp.sub (|
            M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "number" |),
            M.get_name (| globals, "block_number" |)
          |) |) |) in
        M.pure Constant.None_
      )) |) in
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

Definition coinbase : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push the current block's beneficiary address (address of the block miner)
    onto the stack.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

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
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "coinbase" |)
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

Definition timestamp : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push the current block's timestamp onto the stack. Here the timestamp
    being referred is actually the unix timestamp in seconds.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

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
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "time" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition number : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push the current block's number onto the stack.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

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
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "number" |)
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

Definition difficulty : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push the current block's difficulty onto the stack.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

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
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "difficulty" |)
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

Definition gas_limit : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Push the current block's gas limit onto the stack.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

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
          M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "env" |), "gas_limit" |)
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
