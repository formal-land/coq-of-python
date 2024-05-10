Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Gas
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

EVM gas constants and calculators.
".

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require typing.
Axiom typing_List :
  IsGlobalAlias globals typing.globals "List".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.trace.
Axiom ethereum_trace_GasAndRefund :
  IsGlobalAlias globals ethereum.trace.globals "GasAndRefund".
Axiom ethereum_trace_evm_trace :
  IsGlobalAlias globals ethereum.trace.globals "evm_trace".

Require ethereum.utils.numeric.
Axiom ethereum_utils_numeric_ceil32 :
  IsGlobalAlias globals ethereum.utils.numeric.globals "ceil32".

Require ethereum.gray_glacier.vm.__init__.
Axiom ethereum_gray_glacier_vm___init___Evm :
  IsGlobalAlias globals ethereum.gray_glacier.vm.__init__.globals "Evm".

Require ethereum.gray_glacier.vm.exceptions.
Axiom ethereum_gray_glacier_vm_exceptions_OutOfGasError :
  IsGlobalAlias globals ethereum.gray_glacier.vm.exceptions.globals "OutOfGasError".

Definition GAS_JUMPDEST : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 1
    ],
    make_dict []
  |)
)).

Definition GAS_BASE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 2
    ],
    make_dict []
  |)
)).

Definition GAS_VERY_LOW : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_STORAGE_SET : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 20000
    ],
    make_dict []
  |)
)).

Definition GAS_STORAGE_UPDATE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 5000
    ],
    make_dict []
  |)
)).

Definition GAS_STORAGE_CLEAR_REFUND : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 4800
    ],
    make_dict []
  |)
)).

Definition GAS_LOW : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 5
    ],
    make_dict []
  |)
)).

Definition GAS_MID : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 8
    ],
    make_dict []
  |)
)).

Definition GAS_HIGH : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 10
    ],
    make_dict []
  |)
)).

Definition GAS_EXPONENTIATION : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 10
    ],
    make_dict []
  |)
)).

Definition GAS_EXPONENTIATION_PER_BYTE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 50
    ],
    make_dict []
  |)
)).

Definition GAS_MEMORY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_KECCAK256 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 30
    ],
    make_dict []
  |)
)).

Definition GAS_KECCAK256_WORD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 6
    ],
    make_dict []
  |)
)).

Definition GAS_COPY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_BLOCK_HASH : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 20
    ],
    make_dict []
  |)
)).

Definition GAS_LOG : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 375
    ],
    make_dict []
  |)
)).

Definition GAS_LOG_DATA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 8
    ],
    make_dict []
  |)
)).

Definition GAS_LOG_TOPIC : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 375
    ],
    make_dict []
  |)
)).

Definition GAS_CREATE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 32000
    ],
    make_dict []
  |)
)).

Definition GAS_CODE_DEPOSIT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 200
    ],
    make_dict []
  |)
)).

Definition GAS_ZERO : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 0
    ],
    make_dict []
  |)
)).

Definition GAS_NEW_ACCOUNT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 25000
    ],
    make_dict []
  |)
)).

Definition GAS_CALL_VALUE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 9000
    ],
    make_dict []
  |)
)).

Definition GAS_CALL_STIPEND : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 2300
    ],
    make_dict []
  |)
)).

Definition GAS_SELF_DESTRUCT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 5000
    ],
    make_dict []
  |)
)).

Definition GAS_SELF_DESTRUCT_NEW_ACCOUNT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 25000
    ],
    make_dict []
  |)
)).

Definition GAS_ECRECOVER : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 3000
    ],
    make_dict []
  |)
)).

Definition GAS_SHA256 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 60
    ],
    make_dict []
  |)
)).

Definition GAS_SHA256_WORD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 12
    ],
    make_dict []
  |)
)).

Definition GAS_RIPEMD160 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 600
    ],
    make_dict []
  |)
)).

Definition GAS_RIPEMD160_WORD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 120
    ],
    make_dict []
  |)
)).

Definition GAS_IDENTITY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 15
    ],
    make_dict []
  |)
)).

Definition GAS_IDENTITY_WORD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_RETURN_DATA_COPY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_FAST_STEP : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 5
    ],
    make_dict []
  |)
)).

Definition GAS_BLAKE2_PER_ROUND : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 1
    ],
    make_dict []
  |)
)).

Definition GAS_COLD_SLOAD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 2100
    ],
    make_dict []
  |)
)).

Definition GAS_COLD_ACCOUNT_ACCESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 2600
    ],
    make_dict []
  |)
)).

Definition GAS_WARM_ACCESS : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 100
    ],
    make_dict []
  |)
)).

Definition ExtendMemory : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition MessageCallGas : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition charge_gas : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm"; "amount" ] |) in
    let _ := Constant.str "
    Subtracts `amount` from `evm.gas_left`.

    Parameters
    ----------
    evm :
        The current EVM.
    amount :
        The amount of gas the current operation requires.

    " in
    let _ := M.call (|
    M.get_name (| globals, "evm_trace" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.call (|
        M.get_name (| globals, "GasAndRefund" |),
        make_list [
          M.get_name (| globals, "amount" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
          M.get_name (| globals, "amount" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some(M.get_name (| globals, "OutOfGasError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_op (|
          BinOp.sub,
          M.get_field (| M.get_name (| globals, "evm" |), "gas_left" |),
          M.call (|
    M.get_name (| globals, "U256" |),
    make_list [
      M.get_name (| globals, "amount" |)
    ],
    make_dict []
  |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition calculate_memory_gas_cost : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "size_in_bytes" ] |) in
    let _ := Constant.str "
    Calculates the gas cost for allocating memory
    to the smallest multiple of 32 bytes,
    such that the allocated size is at least as big as the given size.

    Parameters
    ----------
    size_in_bytes :
        The size of the data in bytes.

    Returns
    -------
    total_gas_cost : `ethereum.base_types.Uint`
        The gas cost for storing data in memory.
    " in
    let size_in_words :=
      BinOp.floor_div (|
        M.call (|
          M.get_name (| globals, "ceil32" |),
          make_list [
            M.get_name (| globals, "size_in_bytes" |)
          ],
          make_dict []
        |),
        Constant.int 32
      |) in
    let linear_cost :=
      BinOp.mult (|
        M.get_name (| globals, "size_in_words" |),
        M.get_name (| globals, "GAS_MEMORY" |)
      |) in
    let quadratic_cost :=
      BinOp.floor_div (|
        BinOp.pow (|
          M.get_name (| globals, "size_in_words" |),
          Constant.int 2
        |),
        Constant.int 512
      |) in
    let total_gas_cost :=
      BinOp.add (|
        M.get_name (| globals, "linear_cost" |),
        M.get_name (| globals, "quadratic_cost" |)
      |) in
(* At stmt: unsupported node type: Try *)
    M.pure Constant.None_)).

Definition calculate_gas_extend_memory : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "memory"; "extensions" ] |) in
    let _ := Constant.str "
    Calculates the gas amount to extend memory

    Parameters
    ----------
    memory :
        Memory contents of the EVM.
    extensions:
        List of extensions to be made to the memory.
        Consists of a tuple of start position and size.

    Returns
    -------
    extend_memory: `ExtendMemory`
    " in
    let size_to_extend :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |) in
    let to_be_paid :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |) in
    let current_size :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "memory" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    For make_tuple [ M.get_name (| globals, "start_position" |); M.get_name (| globals, "size" |) ] in M.get_name (| globals, "extensions" |) do
      let _ :=
        (* if *)
        M.if_then_else (|
          Compare.eq (|
            M.get_name (| globals, "size" |),
            Constant.int 0
          |),
        (* then *)
        ltac:(M.monadic (
          let _ := M.continue (| |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          M.pure Constant.None_
        )) |) in
      let before_size :=
        M.call (|
          M.get_name (| globals, "ceil32" |),
          make_list [
            M.get_name (| globals, "current_size" |)
          ],
          make_dict []
        |) in
      let after_size :=
        M.call (|
          M.get_name (| globals, "ceil32" |),
          make_list [
            BinOp.add (|
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  M.get_name (| globals, "start_position" |)
                ],
                make_dict []
              |),
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  M.get_name (| globals, "size" |)
                ],
                make_dict []
              |)
            |)
          ],
          make_dict []
        |) in
      let _ :=
        (* if *)
        M.if_then_else (|
          Compare.lt_e (|
            M.get_name (| globals, "after_size" |),
            M.get_name (| globals, "before_size" |)
          |),
        (* then *)
        ltac:(M.monadic (
          let _ := M.continue (| |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          M.pure Constant.None_
        )) |) in
      let size_to_extend := BinOp.add
        BinOp.sub (|
    M.get_name (| globals, "after_size" |),
    M.get_name (| globals, "before_size" |)
  |)
        BinOp.sub (|
    M.get_name (| globals, "after_size" |),
    M.get_name (| globals, "before_size" |)
  |) in
      let already_paid :=
        M.call (|
          M.get_name (| globals, "calculate_memory_gas_cost" |),
          make_list [
            M.get_name (| globals, "before_size" |)
          ],
          make_dict []
        |) in
      let total_cost :=
        M.call (|
          M.get_name (| globals, "calculate_memory_gas_cost" |),
          make_list [
            M.get_name (| globals, "after_size" |)
          ],
          make_dict []
        |) in
      let to_be_paid := BinOp.add
        BinOp.sub (|
    M.get_name (| globals, "total_cost" |),
    M.get_name (| globals, "already_paid" |)
  |)
        BinOp.sub (|
    M.get_name (| globals, "total_cost" |),
    M.get_name (| globals, "already_paid" |)
  |) in
      let current_size :=
        M.get_name (| globals, "after_size" |) in
    EndFor.
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "ExtendMemory" |),
        make_list [
          M.get_name (| globals, "to_be_paid" |);
          M.get_name (| globals, "size_to_extend" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition calculate_message_call_gas : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "value"; "gas"; "gas_left"; "memory_cost"; "extra_gas"; "call_stipend" ] |) in
    let _ := Constant.str "
    Calculates the MessageCallGas (cost and stipend) for
    executing call Opcodes.

    Parameters
    ----------
    value:
        The amount of `ETH` that needs to be transferred.
    gas :
        The amount of gas provided to the message-call.
    gas_left :
        The amount of gas left in the current frame.
    memory_cost :
        The amount needed to extend the memory in the current frame.
    extra_gas :
        The amount of gas needed for transferring value + creating a new
        account inside a message call.
    call_stipend :
        The amount of stipend provided to a message call to execute code while
        transferring value(ETH).

    Returns
    -------
    message_call_gas: `MessageCallGas`
    " in
    let call_stipend :=
            (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "value" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
M.call (|
          M.get_name (| globals, "Uint" |),
          make_list [
            Constant.int 0
          ],
          make_dict []
        |)
      (* else *)
      )), ltac:(M.monadic (
M.get_name (| globals, "call_stipend" |)
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, "gas_left" |),
          BinOp.add (|
            M.get_name (| globals, "extra_gas" |),
            M.get_name (| globals, "memory_cost" |)
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "MessageCallGas" |),
            make_list [
              BinOp.add (|
                M.get_name (| globals, "gas" |),
                M.get_name (| globals, "extra_gas" |)
              |);
              BinOp.add (|
                M.get_name (| globals, "gas" |),
                M.get_name (| globals, "call_stipend" |)
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let gas :=
      M.call (|
        M.get_name (| globals, "min" |),
        make_list [
          M.get_name (| globals, "gas" |);
          M.call (|
            M.get_name (| globals, "max_message_call_gas" |),
            make_list [
              BinOp.sub (|
                BinOp.sub (|
                  M.get_name (| globals, "gas_left" |),
                  M.get_name (| globals, "memory_cost" |)
                |),
                M.get_name (| globals, "extra_gas" |)
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "MessageCallGas" |),
        make_list [
          BinOp.add (|
            M.get_name (| globals, "gas" |),
            M.get_name (| globals, "extra_gas" |)
          |);
          BinOp.add (|
            M.get_name (| globals, "gas" |),
            M.get_name (| globals, "call_stipend" |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition max_message_call_gas : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "gas" ] |) in
    let _ := Constant.str "
    Calculates the maximum gas that is allowed for making a message call

    Parameters
    ----------
    gas :
        The amount of gas provided to the message-call.

    Returns
    -------
    max_allowed_message_call_gas: `ethereum.base_types.Uint`
        The maximum gas allowed for making the message-call.
    " in
    let _ := M.return_ (|
      BinOp.sub (|
        M.get_name (| globals, "gas" |),
        BinOp.floor_div (|
          M.get_name (| globals, "gas" |),
          Constant.int 64
        |)
      |)
    |) in
    M.pure Constant.None_)).
