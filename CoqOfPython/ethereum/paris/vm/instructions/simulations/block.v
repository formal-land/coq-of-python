Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Definition U255_CEIL_VALUE := base_types.U255_CEIL_VALUE.
Module U256 := base_types.U256.
Definition U256_CEIL_VALUE := base_types.U256_CEIL_VALUE.
Module Uint := base_types.Uint.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.
Module Environment := __init__.Environment.

Require ethereum.paris.vm.simulations.gas.
Definition GAS_BLOCK_HASH := gas.GAS_BLOCK_HASH.
Definition GAS_BASE := gas.GAS_BASE.
Definition charge_gas := gas.charge_gas.

Require ethereum.paris.vm.simulations.stack.
Definition pop := stack.pop.
Definition push := stack.push.

Import simulations.CoqOfPython.Notations.

(* def block_hash(evm: Evm) -> None:
    """
    Push the hash of one of the 256 most recent complete blocks onto the
    stack. The block number to hash is present at the top of the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    Raises
    ------
    :py:class:`~ethereum.paris.vm.exceptions.StackUnderflowError`
        If `len(stack)` is less than `1`.
    :py:class:`~ethereum.paris.vm.exceptions.OutOfGasError`
        If `evm.gas_left` is less than `20`.
    """
    # STACK
    block_number = pop(evm.stack)

    # GAS
    charge_gas(evm, GAS_BLOCK_HASH)

    # OPERATION
    if evm.env.number <= block_number or evm.env.number > block_number + 256:
        # Default hash to 0, if the block of interest is not yet on the chain
        # (including the block which has the current executing transaction),
        # or if the block's age is more than 256.
        hash = b"\x00"
    else:
        hash = evm.env.block_hashes[-(evm.env.number - block_number)]

    push(evm.stack, U256.from_be_bytes(hash))

    # PROGRAM COUNTER
    evm.pc += 1 *)

Definition block_hash : MS? Evm.t Exception.t unit := 
    (* STACK *)
    letS? block_number := StateError.lift_lens Evm.Lens.stack pop in
    (* GAS *)
    letS? _ := charge_gas GAS_BLOCK_HASH in
    (* OPERATION *)
    (* Get the Evm.Rest.env.number *)
    letS? evm := readS? in
    let '(Evm.Make _ rest) := evm in
    let evm_env_number := rest.(Evm.Rest.env).(Environment.number) in
    (* Get the Evm.Rest.env.block_hashes *)
    let evm_env_block_hashes := rest.(Evm.Rest.env).(Environment.block_hashes) in

    (* Construct correrctly the b"\x00" *)
    let b := base_types.FixedBytes.Make [Ascii.ascii_of_N 0] in
    let b1 := hash.Bytes32.Make b in
    let b_x00 := __init__.Hash32.Make b1 in

    let hash := if (orb (Uint.get evm_env_number <=? U256.to_Z block_number) 
      (Uint.get evm_env_number >? U256.to_Z block_number + 256))
    then b_x00 (* __init__.Hash32.t *)
    else List.nth 
      (Z.to_nat (-((Uint.get evm_env_number) - (U256.to_Z block_number)))) 
      evm_env_block_hashes
      b_x00 (* Coq's nth function need to provide a default value *)
      in

    (* Translate the type of hash from Hash32 to U256? *)
    let hash := __init__.Hash32.get hash in
    let hash := hash.Bytes32.get hash in
    let hash := base_types.Uint.from_bytes hash in
    let hash := base_types.Uint.get hash in (* UInt to Z for convenience *)
    let hash := U256.of_Z hash in

    letS? _ := StateError.lift_lens Evm.Lens.stack (push hash) in 
    (* PROGRAM COUNTER *) 
    letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
    returnS? tt.

(* def coinbase(evm: Evm) -> None:
    """
    Push the current block's beneficiary address (address of the block miner)
    onto the stack.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

    Parameters
    ----------
    evm :
        The current EVM frame.

    Raises
    ------
    :py:class:`~ethereum.paris.vm.exceptions.StackOverflowError`
        If `len(stack)` is equal to `1024`.
    :py:class:`~ethereum.paris.vm.exceptions.OutOfGasError`
        If `evm.gas_left` is less than `2`.
    """
    # STACK
    pass

    # GAS
    charge_gas(evm, GAS_BASE)

    # OPERATION
    push(evm.stack, U256.from_be_bytes(evm.env.coinbase))

    # PROGRAM COUNTER
    evm.pc += 1 *)

Definition coinbase : MS? Evm.t Exception.t unit := 
    (* GAS *)
    letS? _ := charge_gas GAS_BASE in
    (* Get evm.env.coinbase *)
    letS? evm := readS? in
    let '(Evm.Make _ rest) := evm in
    (* Convert from Address to -> Byte20 -> Bytes -> U256 *)
    let evm_env_coinbase := rest.(Evm.Rest.env).(Environment.coinbase) in
    let evm_env_coinbase := fork_types.Address.get evm_env_coinbase in
    let evm_env_coinbase := base_types.Bytes20.get evm_env_coinbase in
    let evm_env_coinbase := base_types.Uint.from_bytes evm_env_coinbase in
    let evm_env_coinbase := base_types.Uint.get evm_env_coinbase in
    let evm_env_coinbase := U256.of_Z evm_env_coinbase in

    letS? _ := StateError.lift_lens Evm.Lens.stack (push evm_env_coinbase) in 
    (* PROGRAM COUNTER *) 
    letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
    returnS? tt.

(* def timestamp(evm: Evm) -> None:
    """
    Push the current block's timestamp onto the stack. Here the timestamp
    being referred is actually the unix timestamp in seconds.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

    Parameters
    ----------
    evm :
        The current EVM frame.

    Raises
    ------
    :py:class:`~ethereum.paris.vm.exceptions.StackOverflowError`
        If `len(stack)` is equal to `1024`.
    :py:class:`~ethereum.paris.vm.exceptions.OutOfGasError`
        If `evm.gas_left` is less than `2`.
    """
    # STACK
    pass

    # GAS
    charge_gas(evm, GAS_BASE)

    # OPERATION
    push(evm.stack, evm.env.time)

    # PROGRAM COUNTER
    evm.pc += 1 *)
Definition timestamp : MS? Evm.t Exception.t unit := 
  (* GAS *)
  letS? _ := charge_gas GAS_BASE in
  (* Get evm.env.time *)
  letS? evm := readS? in
  let '(Evm.Make _ rest) := evm in
  let evm_env_time := rest.(Evm.Rest.env).(Environment.time) in

  letS? _ := StateError.lift_lens Evm.Lens.stack (push evm_env_time) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* def number(evm: Evm) -> None:
    """
    Push the current block's number onto the stack.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

    Parameters
    ----------
    evm :
        The current EVM frame.

    Raises
    ------
    :py:class:`~ethereum.paris.vm.exceptions.StackOverflowError`
        If `len(stack)` is equal to `1024`.
    :py:class:`~ethereum.paris.vm.exceptions.OutOfGasError`
        If `evm.gas_left` is less than `2`.
    """
    # STACK
    pass

    # GAS
    charge_gas(evm, GAS_BASE)

    # OPERATION
    push(evm.stack, U256(evm.env.number))

    # PROGRAM COUNTER
    evm.pc += 1 *)
Definition number : MS? Evm.t Exception.t unit := 
  (* GAS *)
  letS? _ := charge_gas GAS_BASE in
  (* Get evm.env.number *)
  letS? evm := readS? in
  let '(Evm.Make _ rest) := evm in
  let evm_env_number := rest.(Evm.Rest.env).(Environment.number) in
  (* Conversion from Uint to U256 *)
  let evm_env_number := base_types.Uint.get evm_env_number in
  let evm_env_number := U256.of_Z evm_env_number in

  letS? _ := StateError.lift_lens Evm.Lens.stack (push evm_env_number) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.


(* def prev_randao(evm: Evm) -> None:
    """
    Push the `prev_randao` value onto the stack.

    The `prev_randao` value is the random output of the beacon chain's
    randomness oracle for the previous block.

    Parameters
    ----------
    evm :
        The current EVM frame.

    Raises
    ------
    :py:class:`~ethereum.paris.vm.exceptions.StackOverflowError`
        If `len(stack)` is equal to `1024`.
    :py:class:`~ethereum.paris.vm.exceptions.OutOfGasError`
        If `evm.gas_left` is less than `2`.
    """
    # STACK
    pass

    # GAS
    charge_gas(evm, GAS_BASE)

    # OPERATION
    push(evm.stack, U256.from_be_bytes(evm.env.prev_randao))

    # PROGRAM COUNTER
    evm.pc += 1 *)
Definition prev_randao : MS? Evm.t Exception.t unit := 
  (* GAS *)
  letS? _ := charge_gas GAS_BASE in
  (* Get evm.env.prev_randao *)
  letS? evm := readS? in
  let '(Evm.Make _ rest) := evm in
  let evm_env_prev_randao := rest.(Evm.Rest.env).(Environment.prev_randao) in
  (* Convert the type from Bytes32 to U256 *)
  let evm_env_prev_randao := hash.Bytes32.get evm_env_prev_randao in
  let evm_env_prev_randao := base_types.Uint.from_bytes evm_env_prev_randao in
  let evm_env_prev_randao := base_types.Uint.get evm_env_prev_randao in
  let evm_env_prev_randao := U256.of_Z evm_env_prev_randao in

  letS? _ := StateError.lift_lens Evm.Lens.stack (push evm_env_prev_randao) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.


(* def gas_limit(evm: Evm) -> None:
    """
    Push the current block's gas limit onto the stack.

    Here the current block refers to the block in which the currently
    executing transaction/call resides.

    Parameters
    ----------
    evm :
        The current EVM frame.

    Raises
    ------
    :py:class:`~ethereum.paris.vm.exceptions.StackOverflowError`
        If `len(stack)` is equal to `1024`.
    :py:class:`~ethereum.paris.vm.exceptions.OutOfGasError`
        If `evm.gas_left` is less than `2`.
    """
    # STACK
    pass

    # GAS
    charge_gas(evm, GAS_BASE)

    # OPERATION
    push(evm.stack, U256(evm.env.gas_limit))

    # PROGRAM COUNTER
    evm.pc += 1 *)
Definition gas_limit : MS? Evm.t Exception.t unit := 
  (* GAS *)
  letS? _ := charge_gas GAS_BASE in
  (* Get evm.env.gas_limit *)
  letS? evm := readS? in
  let '(Evm.Make _ rest) := evm in
  let evm_env_gas_limit := rest.(Evm.Rest.env).(Environment.gas_limit) in

  (* letS? _ := StateError.lift_lens Evm.Lens.stack (push evm_env_gas_limit) in  *)
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* 
def chain_id(evm: Evm) -> None:
    """
    Push the chain id onto the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    Raises
    ------
    :py:class:`~ethereum.paris.vm.exceptions.StackOverflowError`
        If `len(stack)` is equal to `1024`.
    :py:class:`~ethereum.paris.vm.exceptions.OutOfGasError`
        If `evm.gas_left` is less than `2`.
    """
    # STACK
    pass

    # GAS
    charge_gas(evm, GAS_BASE)

    # OPERATION
    push(evm.stack, U256(evm.env.chain_id))

    # PROGRAM COUNTER
    evm.pc += 1 *)
Definition chain_id : MS? Evm.t Exception.t unit := 
  (* GAS *)
  letS? _ := charge_gas GAS_BASE in
  (* Get evm.env.chain_id *)
  letS? evm := readS? in
  let '(Evm.Make _ rest) := evm in
  (* Convert from U64 to U256 *)
  let evm_env_chain_id := rest.(Evm.Rest.env).(Environment.chain_id) in
  let '(base_types.U64.Make evm_env_chain_id) := evm_env_chain_id in
  let evm_env_chain_id := base_types.U256.Make evm_env_chain_id in

  letS? _ := StateError.lift_lens Evm.Lens.stack (push evm_env_chain_id) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.