Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.paris.vm.precompiled_contracts.modexp".

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

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U256"; "Bytes"; "Uint" ].

Axiom ethereum_paris_vm_imports :
  AreImported globals "ethereum.paris.vm" [ "Evm" ].

Axiom ethereum_paris_vm_gas_imports :
  AreImported globals "ethereum.paris.vm.gas" [ "charge_gas" ].

Axiom ethereum_paris_vm_memory_imports :
  AreImported globals "ethereum.paris.vm.memory" [ "buffer_read" ].

Definition GQUADDIVISOR : Value.t := M.run ltac:(M.monadic (
  Constant.int 3
)).

Definition modexp : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Calculates `(base**exp) % modulus` for arbitrary sized `base`, `exp` and.
    `modulus`. The return value is the same length as the modulus.
    " in
    let data :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |) in
    let base_length :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |);
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
    let exp_length :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 32
                ],
                make_dict []
              |);
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
    let modulus_length :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 64
                ],
                make_dict []
              |);
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
    let exp_start :=
      BinOp.add (|
        M.call (|
          M.get_name (| globals, "U256" |),
          make_list [
            Constant.int 96
          ],
          make_dict []
        |),
        M.get_name (| globals, "base_length" |)
      |) in
    let exp_head :=
      M.call (|
        M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.get_name (| globals, "exp_start" |);
              M.call (|
                M.get_name (| globals, "min" |),
                make_list [
                  M.call (|
                    M.get_name (| globals, "U256" |),
                    make_list [
                      Constant.int 32
                    ],
                    make_dict []
                  |);
                  M.get_name (| globals, "exp_length" |)
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
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.call (|
        M.get_name (| globals, "gas_cost" |),
        make_list [
          M.get_name (| globals, "base_length" |);
          M.get_name (| globals, "modulus_length" |);
          M.get_name (| globals, "exp_length" |);
          M.get_name (| globals, "exp_head" |)
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
            M.get_name (| globals, "base_length" |),
            Constant.int 0
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_name (| globals, "modulus_length" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, "evm" |), "output" |),
          M.call (|
            M.get_name (| globals, "Bytes" |),
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
    let base :=
      M.call (|
        M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.call (|
                M.get_name (| globals, "U256" |),
                make_list [
                  Constant.int 96
                ],
                make_dict []
              |);
              M.get_name (| globals, "base_length" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let exp :=
      M.call (|
        M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.get_name (| globals, "exp_start" |);
              M.get_name (| globals, "exp_length" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let modulus_start :=
      BinOp.add (|
        M.get_name (| globals, "exp_start" |),
        M.get_name (| globals, "exp_length" |)
      |) in
    let modulus :=
      M.call (|
        M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "buffer_read" |),
            make_list [
              M.get_name (| globals, "data" |);
              M.get_name (| globals, "modulus_start" |);
              M.get_name (| globals, "modulus_length" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "modulus" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, "evm" |), "output" |),
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, "Bytes" |),
              make_list [
                Constant.bytes "00"
              ],
              make_dict []
            |),
            M.get_name (| globals, "modulus_length" |)
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, "evm" |), "output" |),
          M.call (|
            M.get_field (| M.call (|
              M.get_name (| globals, "Uint" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "pow" |),
                  make_list [
                    M.get_name (| globals, "base" |);
                    M.get_name (| globals, "exp" |);
                    M.get_name (| globals, "modulus" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |), "to_bytes" |),
            make_list [
              M.get_name (| globals, "modulus_length" |);
              Constant.str "big"
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition complexity : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "base_length"; "modulus_length" ] |) in
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
    let max_length :=
      M.call (|
        M.get_name (| globals, "max" |),
        make_list [
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "base_length" |)
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "modulus_length" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let words :=
      BinOp.floor_div (|
        BinOp.add (|
          M.get_name (| globals, "max_length" |),
          Constant.int 7
        |),
        Constant.int 8
      |) in
    let _ := M.return_ (|
      BinOp.pow (|
        M.get_name (| globals, "words" |),
        Constant.int 2
      |)
    |) in
    M.pure Constant.None_)).

Definition iterations : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "exponent_length"; "exponent_head" ] |) in
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
            M.get_name (| globals, "exponent_length" |),
            Constant.int 32
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_name (| globals, "exponent_head" |),
              Constant.int 0
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let count :=
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt_e (|
              M.get_name (| globals, "exponent_length" |),
              Constant.int 32
            |),
          (* then *)
          ltac:(M.monadic (
            let bit_length :=
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  M.call (|
                    M.get_field (| M.get_name (| globals, "exponent_head" |), "bit_length" |),
                    make_list [],
                    make_dict []
                  |)
                ],
                make_dict []
              |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.gt (|
                  M.get_name (| globals, "bit_length" |),
                  Constant.int 0
                |),
              (* then *)
              ltac:(M.monadic (
                let bit_length := BinOp.sub
                  Constant.int 1
                  Constant.int 1 in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let count :=
              M.get_name (| globals, "bit_length" |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let length_part :=
              BinOp.mult (|
                Constant.int 8,
                BinOp.sub (|
                  M.call (|
                    M.get_name (| globals, "Uint" |),
                    make_list [
                      M.get_name (| globals, "exponent_length" |)
                    ],
                    make_dict []
                  |),
                  Constant.int 32
                |)
              |) in
            let bits_part :=
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  M.call (|
                    M.get_field (| M.get_name (| globals, "exponent_head" |), "bit_length" |),
                    make_list [],
                    make_dict []
                  |)
                ],
                make_dict []
              |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.gt (|
                  M.get_name (| globals, "bits_part" |),
                  Constant.int 0
                |),
              (* then *)
              ltac:(M.monadic (
                let bits_part := BinOp.sub
                  Constant.int 1
                  Constant.int 1 in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let count :=
              BinOp.add (|
                M.get_name (| globals, "length_part" |),
                M.get_name (| globals, "bits_part" |)
              |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "max" |),
        make_list [
          M.get_name (| globals, "count" |);
          M.call (|
            M.get_name (| globals, "Uint" |),
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

Definition gas_cost : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "base_length"; "modulus_length"; "exponent_length"; "exponent_head" ] |) in
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
    let multiplication_complexity :=
      M.call (|
        M.get_name (| globals, "complexity" |),
        make_list [
          M.get_name (| globals, "base_length" |);
          M.get_name (| globals, "modulus_length" |)
        ],
        make_dict []
      |) in
    let iteration_count :=
      M.call (|
        M.get_name (| globals, "iterations" |),
        make_list [
          M.get_name (| globals, "exponent_length" |);
          M.get_name (| globals, "exponent_head" |)
        ],
        make_dict []
      |) in
    let cost :=
      BinOp.mult (|
        M.get_name (| globals, "multiplication_complexity" |),
        M.get_name (| globals, "iteration_count" |)
      |) in
    let cost := BinOp.floor_div
      M.get_name (| globals, "GQUADDIVISOR" |)
      M.get_name (| globals, "GQUADDIVISOR" |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "max" |),
        make_list [
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              Constant.int 200
            ],
            make_dict []
          |);
          M.get_name (| globals, "cost" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
