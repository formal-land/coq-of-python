Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.byzantium.vm.gas".

Definition locals_stack : list Locals.t := [].

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

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_List :
  IsImported globals "typing" "List".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_trace_imports_GasAndRefund :
  IsImported globals "ethereum.trace" "GasAndRefund".
Axiom ethereum_trace_imports_evm_trace :
  IsImported globals "ethereum.trace" "evm_trace".

Axiom ethereum_utils_numeric_imports_ceil32 :
  IsImported globals "ethereum.utils.numeric" "ceil32".

Axiom ethereum_byzantium_vm_imports_Evm :
  IsImported globals "ethereum.byzantium.vm" "Evm".

Axiom ethereum_byzantium_vm_exceptions_imports_OutOfGasError :
  IsImported globals "ethereum.byzantium.vm.exceptions" "OutOfGasError".

Definition GAS_JUMPDEST : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 1
    ],
    make_dict []
  |)
)).

Definition GAS_BASE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 2
    ],
    make_dict []
  |)
)).

Definition GAS_VERY_LOW : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_SLOAD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 200
    ],
    make_dict []
  |)
)).

Definition GAS_STORAGE_SET : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 20000
    ],
    make_dict []
  |)
)).

Definition GAS_STORAGE_UPDATE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 5000
    ],
    make_dict []
  |)
)).

Definition GAS_STORAGE_CLEAR_REFUND : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 15000
    ],
    make_dict []
  |)
)).

Definition GAS_LOW : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 5
    ],
    make_dict []
  |)
)).

Definition GAS_MID : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 8
    ],
    make_dict []
  |)
)).

Definition GAS_HIGH : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 10
    ],
    make_dict []
  |)
)).

Definition GAS_EXPONENTIATION : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 10
    ],
    make_dict []
  |)
)).

Definition GAS_EXPONENTIATION_PER_BYTE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 50
    ],
    make_dict []
  |)
)).

Definition GAS_MEMORY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_KECCAK256 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 30
    ],
    make_dict []
  |)
)).

Definition GAS_KECCAK256_WORD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 6
    ],
    make_dict []
  |)
)).

Definition GAS_COPY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_BLOCK_HASH : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 20
    ],
    make_dict []
  |)
)).

Definition GAS_EXTERNAL : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 700
    ],
    make_dict []
  |)
)).

Definition GAS_BALANCE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 400
    ],
    make_dict []
  |)
)).

Definition GAS_LOG : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 375
    ],
    make_dict []
  |)
)).

Definition GAS_LOG_DATA : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 8
    ],
    make_dict []
  |)
)).

Definition GAS_LOG_TOPIC : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 375
    ],
    make_dict []
  |)
)).

Definition GAS_CREATE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 32000
    ],
    make_dict []
  |)
)).

Definition GAS_CODE_DEPOSIT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 200
    ],
    make_dict []
  |)
)).

Definition GAS_ZERO : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 0
    ],
    make_dict []
  |)
)).

Definition GAS_CALL : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 700
    ],
    make_dict []
  |)
)).

Definition GAS_NEW_ACCOUNT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 25000
    ],
    make_dict []
  |)
)).

Definition GAS_CALL_VALUE : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 9000
    ],
    make_dict []
  |)
)).

Definition GAS_CALL_STIPEND : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 2300
    ],
    make_dict []
  |)
)).

Definition GAS_SELF_DESTRUCT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 5000
    ],
    make_dict []
  |)
)).

Definition GAS_SELF_DESTRUCT_NEW_ACCOUNT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 25000
    ],
    make_dict []
  |)
)).

Definition REFUND_SELF_DESTRUCT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 24000
    ],
    make_dict []
  |)
)).

Definition GAS_ECRECOVER : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 3000
    ],
    make_dict []
  |)
)).

Definition GAS_SHA256 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 60
    ],
    make_dict []
  |)
)).

Definition GAS_SHA256_WORD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 12
    ],
    make_dict []
  |)
)).

Definition GAS_RIPEMD160 : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 600
    ],
    make_dict []
  |)
)).

Definition GAS_RIPEMD160_WORD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 120
    ],
    make_dict []
  |)
)).

Definition GAS_IDENTITY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 15
    ],
    make_dict []
  |)
)).

Definition GAS_IDENTITY_WORD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition GAS_RETURN_DATA_COPY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 3
    ],
    make_dict []
  |)
)).

Definition ExtendMemory : Value.t := make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition MessageCallGas : Value.t := make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition charge_gas : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm"; "amount" ] in
    ltac:(M.monadic (
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
    M.get_name (| globals, locals_stack, "evm_trace" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.call (|
        M.get_name (| globals, locals_stack, "GasAndRefund" |),
        make_list [
          M.get_name (| globals, locals_stack, "amount" |)
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
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |),
          M.get_name (| globals, locals_stack, "amount" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "OutOfGasError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_op (|
          BinOp.sub,
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "gas_left" |),
          M.call (|
    M.get_name (| globals, locals_stack, "U256" |),
    make_list [
      M.get_name (| globals, locals_stack, "amount" |)
    ],
    make_dict []
  |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom charge_gas_in_globals :
  IsInGlobals globals "charge_gas" (make_function charge_gas).

Definition calculate_memory_gas_cost : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "size_in_bytes" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "size_in_words" ,
      BinOp.floor_div (|
        M.call (|
          M.get_name (| globals, locals_stack, "ceil32" |),
          make_list [
            M.get_name (| globals, locals_stack, "size_in_bytes" |)
          ],
          make_dict []
        |),
        Constant.int 32
      |)
    |) in
    let _ := M.assign_local (|
      "linear_cost" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "size_in_words" |),
        M.get_name (| globals, locals_stack, "GAS_MEMORY" |)
      |)
    |) in
    let _ := M.assign_local (|
      "quadratic_cost" ,
      BinOp.floor_div (|
        BinOp.pow (|
          M.get_name (| globals, locals_stack, "size_in_words" |),
          Constant.int 2
        |),
        Constant.int 512
      |)
    |) in
    let _ := M.assign_local (|
      "total_gas_cost" ,
      BinOp.add (|
        M.get_name (| globals, locals_stack, "linear_cost" |),
        M.get_name (| globals, locals_stack, "quadratic_cost" |)
      |)
    |) in
(* At stmt: unsupported node type: Try *)
    M.pure Constant.None_)).

Axiom calculate_memory_gas_cost_in_globals :
  IsInGlobals globals "calculate_memory_gas_cost" (make_function calculate_memory_gas_cost).

Definition calculate_gas_extend_memory : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "memory"; "extensions" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "size_to_extend" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "to_be_paid" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "current_size" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "memory" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      M.for_ (|
        make_tuple [ M.get_name (| globals, locals_stack, "start_position" |); M.get_name (| globals, locals_stack, "size" |) ],
        M.get_name (| globals, locals_stack, "extensions" |),
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.eq (|
                M.get_name (| globals, locals_stack, "size" |),
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
          let _ := M.assign_local (|
            "before_size" ,
            M.call (|
              M.get_name (| globals, locals_stack, "ceil32" |),
              make_list [
                M.get_name (| globals, locals_stack, "current_size" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "after_size" ,
            M.call (|
              M.get_name (| globals, locals_stack, "ceil32" |),
              make_list [
                BinOp.add (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "Uint" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "start_position" |)
                    ],
                    make_dict []
                  |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "Uint" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "size" |)
                    ],
                    make_dict []
                  |)
                |)
              ],
              make_dict []
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt_e (|
                M.get_name (| globals, locals_stack, "after_size" |),
                M.get_name (| globals, locals_stack, "before_size" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.continue (| |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_op_local (|
            BinOp.add,
            "size_to_extend",
            BinOp.sub (|
    M.get_name (| globals, locals_stack, "after_size" |),
    M.get_name (| globals, locals_stack, "before_size" |)
  |)
          |) in
          let _ := M.assign_local (|
            "already_paid" ,
            M.call (|
              M.get_name (| globals, locals_stack, "calculate_memory_gas_cost" |),
              make_list [
                M.get_name (| globals, locals_stack, "before_size" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "total_cost" ,
            M.call (|
              M.get_name (| globals, locals_stack, "calculate_memory_gas_cost" |),
              make_list [
                M.get_name (| globals, locals_stack, "after_size" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_op_local (|
            BinOp.add,
            "to_be_paid",
            BinOp.sub (|
    M.get_name (| globals, locals_stack, "total_cost" |),
    M.get_name (| globals, locals_stack, "already_paid" |)
  |)
          |) in
          let _ := M.assign_local (|
            "current_size" ,
            M.get_name (| globals, locals_stack, "after_size" |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "ExtendMemory" |),
        make_list [
          M.get_name (| globals, locals_stack, "to_be_paid" |);
          M.get_name (| globals, locals_stack, "size_to_extend" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom calculate_gas_extend_memory_in_globals :
  IsInGlobals globals "calculate_gas_extend_memory" (make_function calculate_gas_extend_memory).

Definition calculate_message_call_gas : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "value"; "gas"; "gas_left"; "memory_cost"; "extra_gas"; "call_stipend" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "call_stipend" ,
            (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "value" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
M.call (|
          M.get_name (| globals, locals_stack, "Uint" |),
          make_list [
            Constant.int 0
          ],
          make_dict []
        |)
      (* else *)
      )), ltac:(M.monadic (
M.get_name (| globals, locals_stack, "call_stipend" |)
      )) |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, locals_stack, "gas_left" |),
          BinOp.add (|
            M.get_name (| globals, locals_stack, "extra_gas" |),
            M.get_name (| globals, locals_stack, "memory_cost" |)
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "MessageCallGas" |),
            make_list [
              BinOp.add (|
                M.get_name (| globals, locals_stack, "gas" |),
                M.get_name (| globals, locals_stack, "extra_gas" |)
              |);
              BinOp.add (|
                M.get_name (| globals, locals_stack, "gas" |),
                M.get_name (| globals, locals_stack, "call_stipend" |)
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
    let _ := M.assign_local (|
      "gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "min" |),
        make_list [
          M.get_name (| globals, locals_stack, "gas" |);
          M.call (|
            M.get_name (| globals, locals_stack, "max_message_call_gas" |),
            make_list [
              BinOp.sub (|
                BinOp.sub (|
                  M.get_name (| globals, locals_stack, "gas_left" |),
                  M.get_name (| globals, locals_stack, "memory_cost" |)
                |),
                M.get_name (| globals, locals_stack, "extra_gas" |)
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "MessageCallGas" |),
        make_list [
          BinOp.add (|
            M.get_name (| globals, locals_stack, "gas" |),
            M.get_name (| globals, locals_stack, "extra_gas" |)
          |);
          BinOp.add (|
            M.get_name (| globals, locals_stack, "gas" |),
            M.get_name (| globals, locals_stack, "call_stipend" |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom calculate_message_call_gas_in_globals :
  IsInGlobals globals "calculate_message_call_gas" (make_function calculate_message_call_gas).

Definition max_message_call_gas : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "gas" ] in
    ltac:(M.monadic (
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
        M.get_name (| globals, locals_stack, "gas" |),
        BinOp.floor_div (|
          M.get_name (| globals, locals_stack, "gas" |),
          Constant.int 64
        |)
      |)
    |) in
    M.pure Constant.None_)).

Axiom max_message_call_gas_in_globals :
  IsInGlobals globals "max_message_call_gas" (make_function max_message_call_gas).
