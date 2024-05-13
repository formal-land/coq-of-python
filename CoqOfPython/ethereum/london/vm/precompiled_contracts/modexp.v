Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.london.vm.precompiled_contracts.modexp".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) MODEXP PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the `MODEXP` precompiled contract.
".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_london_vm_imports_Evm :
  IsImported globals "ethereum.london.vm" "Evm".

Axiom ethereum_london_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.london.vm.gas" "charge_gas".

Axiom ethereum_london_vm_memory_imports_buffer_read :
  IsImported globals "ethereum.london.vm.memory" "buffer_read".

Definition GQUADDIVISOR : Value.t := M.run ltac:(M.monadic (
  Constant.int 3
)).

Definition modexp : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Calculates `(base**exp) % modulus` for arbitrary sized `base`, `exp` and.
    `modulus`. The return value is the same length as the modulus.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.assign_local (|
      "base_length" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |);
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
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "exp_length" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  Constant.int 32
                ],
                make_dict []
              |);
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
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "modulus_length" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  Constant.int 64
                ],
                make_dict []
              |);
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
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "exp_start" ,
      BinOp.add (|
        M.call (|
          M.get_name (| globals, locals_stack, "U256" |),
          make_list [
            Constant.int 96
          ],
          make_dict []
        |),
        M.get_name (| globals, locals_stack, "base_length" |)
      |)
    |) in
    let _ := M.assign_local (|
      "exp_head" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.get_name (| globals, locals_stack, "exp_start" |);
              M.call (|
                M.get_name (| globals, locals_stack, "min" |),
                make_list [
                  M.call (|
                    M.get_name (| globals, locals_stack, "U256" |),
                    make_list [
                      Constant.int 32
                    ],
                    make_dict []
                  |);
                  M.get_name (| globals, locals_stack, "exp_length" |)
                ],
                make_dict []
              |)
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
      M.call (|
        M.get_name (| globals, locals_stack, "gas_cost" |),
        make_list [
          M.get_name (| globals, locals_stack, "base_length" |);
          M.get_name (| globals, locals_stack, "modulus_length" |);
          M.get_name (| globals, locals_stack, "exp_length" |);
          M.get_name (| globals, locals_stack, "exp_head" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.eq (|
            M.get_name (| globals, locals_stack, "base_length" |),
            Constant.int 0
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_name (| globals, locals_stack, "modulus_length" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
          M.call (|
            M.get_name (| globals, locals_stack, "Bytes" |),
            make_list [],
            make_dict []
          |)
        |) in
        let _ := M.return_ (|
          Constant.None_
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "base" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.call (|
                M.get_name (| globals, locals_stack, "U256" |),
                make_list [
                  Constant.int 96
                ],
                make_dict []
              |);
              M.get_name (| globals, locals_stack, "base_length" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "exp" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.get_name (| globals, locals_stack, "exp_start" |);
              M.get_name (| globals, locals_stack, "exp_length" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "modulus_start" ,
      BinOp.add (|
        M.get_name (| globals, locals_stack, "exp_start" |),
        M.get_name (| globals, locals_stack, "exp_length" |)
      |)
    |) in
    let _ := M.assign_local (|
      "modulus" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "buffer_read" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |);
              M.get_name (| globals, locals_stack, "modulus_start" |);
              M.get_name (| globals, locals_stack, "modulus_length" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "modulus" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, locals_stack, "Bytes" |),
              make_list [
                Constant.bytes "00"
              ],
              make_dict []
            |),
            M.get_name (| globals, locals_stack, "modulus_length" |)
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
          M.call (|
            M.get_field (| M.call (|
              M.get_name (| globals, locals_stack, "Uint" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "pow" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "base" |);
                    M.get_name (| globals, locals_stack, "exp" |);
                    M.get_name (| globals, locals_stack, "modulus" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |), "to_bytes" |),
            make_list [
              M.get_name (| globals, locals_stack, "modulus_length" |);
              Constant.str "big"
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom modexp_in_globals :
  IsInGlobals globals "modexp" (make_function modexp).

Definition complexity : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "base_length"; "modulus_length" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Estimate the complexity of performing a modular exponentiation.

    Parameters
    ----------

    base_length :
        Length of the array representing the base integer.

    modulus_length :
        Length of the array representing the modulus integer.

    Returns
    -------

    complexity : `Uint`
        Complexity of performing the operation.
    " in
    let _ := M.assign_local (|
      "max_length" ,
      M.call (|
        M.get_name (| globals, locals_stack, "max" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_name (| globals, locals_stack, "base_length" |)
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_name (| globals, locals_stack, "modulus_length" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "words" ,
      BinOp.floor_div (|
        BinOp.add (|
          M.get_name (| globals, locals_stack, "max_length" |),
          Constant.int 7
        |),
        Constant.int 8
      |)
    |) in
    let _ := M.return_ (|
      BinOp.pow (|
        M.get_name (| globals, locals_stack, "words" |),
        Constant.int 2
      |)
    |) in
    M.pure Constant.None_)).

Axiom complexity_in_globals :
  IsInGlobals globals "complexity" (make_function complexity).

Definition iterations : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "exponent_length"; "exponent_head" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Calculate the number of iterations required to perform a modular
    exponentiation.

    Parameters
    ----------

    exponent_length :
        Length of the array representing the exponent integer.

    exponent_head :
        First 32 bytes of the exponent (with leading zero padding if it is
        shorter than 32 bytes), as an unsigned integer.

    Returns
    -------

    iterations : `Uint`
        Number of iterations.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.and (|
          Compare.lt_e (|
            M.get_name (| globals, locals_stack, "exponent_length" |),
            Constant.int 32
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_name (| globals, locals_stack, "exponent_head" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "count" ,
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt_e (|
              M.get_name (| globals, locals_stack, "exponent_length" |),
              Constant.int 32
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "bit_length" ,
              M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "exponent_head" |), "bit_length" |),
                    make_list [],
                    make_dict []
                  |)
                ],
                make_dict []
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.gt (|
                  M.get_name (| globals, locals_stack, "bit_length" |),
                  Constant.int 0
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.assign_op_local (|
                  BinOp.sub,
                  "bit_length",
                  Constant.int 1
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ := M.assign_local (|
              "count" ,
              M.get_name (| globals, locals_stack, "bit_length" |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "length_part" ,
              BinOp.mult (|
                Constant.int 8,
                BinOp.sub (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "Uint" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "exponent_length" |)
                    ],
                    make_dict []
                  |),
                  Constant.int 32
                |)
              |)
            |) in
            let _ := M.assign_local (|
              "bits_part" ,
              M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "exponent_head" |), "bit_length" |),
                    make_list [],
                    make_dict []
                  |)
                ],
                make_dict []
              |)
            |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.gt (|
                  M.get_name (| globals, locals_stack, "bits_part" |),
                  Constant.int 0
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.assign_op_local (|
                  BinOp.sub,
                  "bits_part",
                  Constant.int 1
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ := M.assign_local (|
              "count" ,
              BinOp.add (|
                M.get_name (| globals, locals_stack, "length_part" |),
                M.get_name (| globals, locals_stack, "bits_part" |)
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "max" |),
        make_list [
          M.get_name (| globals, locals_stack, "count" |);
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              Constant.int 1
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom iterations_in_globals :
  IsInGlobals globals "iterations" (make_function iterations).

Definition gas_cost : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "base_length"; "modulus_length"; "exponent_length"; "exponent_head" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Calculate the gas cost of performing a modular exponentiation.

    Parameters
    ----------

    base_length :
        Length of the array representing the base integer.

    modulus_length :
        Length of the array representing the modulus integer.

    exponent_length :
        Length of the array representing the exponent integer.

    exponent_head :
        First 32 bytes of the exponent (with leading zero padding if it is
        shorter than 32 bytes), as an unsigned integer.

    Returns
    -------

    gas_cost : `Uint`
        Gas required for performing the operation.
    " in
    let _ := M.assign_local (|
      "multiplication_complexity" ,
      M.call (|
        M.get_name (| globals, locals_stack, "complexity" |),
        make_list [
          M.get_name (| globals, locals_stack, "base_length" |);
          M.get_name (| globals, locals_stack, "modulus_length" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "iteration_count" ,
      M.call (|
        M.get_name (| globals, locals_stack, "iterations" |),
        make_list [
          M.get_name (| globals, locals_stack, "exponent_length" |);
          M.get_name (| globals, locals_stack, "exponent_head" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "cost" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "multiplication_complexity" |),
        M.get_name (| globals, locals_stack, "iteration_count" |)
      |)
    |) in
    let _ := M.assign_op_local (|
      BinOp.floor_div,
      "cost",
      M.get_name (| globals, locals_stack, "GQUADDIVISOR" |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "max" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              Constant.int 200
            ],
            make_dict []
          |);
          M.get_name (| globals, locals_stack, "cost" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom gas_cost_in_globals :
  IsInGlobals globals "gas_cost" (make_function gas_cost).
