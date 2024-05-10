Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.muir_glacier.vm.__init__.
Axiom ethereum_muir_glacier_vm___init___Evm :
  IsGlobalAlias globals ethereum.muir_glacier.vm.__init__.globals "Evm".

Require ethereum.muir_glacier.vm.gas.
Axiom ethereum_muir_glacier_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.muir_glacier.vm.gas.globals "charge_gas".

Require ethereum.muir_glacier.vm.memory.
Axiom ethereum_muir_glacier_vm_memory_buffer_read :
  IsGlobalAlias globals ethereum.muir_glacier.vm.memory.globals "buffer_read".

Definition GQUADDIVISOR : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 20
    ],
    make_dict []
  |)
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
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
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
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, "exp_length" |),
          Constant.int 32
        |),
      (* then *)
      ltac:(M.monadic (
        let adjusted_exp_length :=
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.call (|
                M.get_name (| globals, "max" |),
                make_list [
                  Constant.int 0;
                  BinOp.sub (|
                    M.call (|
                      M.get_field (| M.get_name (| globals, "exp_head" |), "bit_length" |),
                      make_list [],
                      make_dict []
                    |),
                    Constant.int 1
                  |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let adjusted_exp_length :=
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              BinOp.add (|
                BinOp.mult (|
                  Constant.int 8,
                  BinOp.sub (|
                    M.call (|
                      M.get_name (| globals, "int" |),
                      make_list [
                        M.get_name (| globals, "exp_length" |)
                      ],
                      make_dict []
                    |),
                    Constant.int 32
                  |)
                |),
                M.call (|
                  M.get_name (| globals, "max" |),
                  make_list [
                    Constant.int 0;
                    BinOp.sub (|
                      M.call (|
                        M.get_field (| M.get_name (| globals, "exp_head" |), "bit_length" |),
                        make_list [],
                        make_dict []
                      |),
                      Constant.int 1
                    |)
                  ],
                  make_dict []
                |)
              |)
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.floor_div (|
        BinOp.mult (|
          M.call (|
            M.get_name (| globals, "get_mult_complexity" |),
            make_list [
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  M.call (|
                    M.get_name (| globals, "max" |),
                    make_list [
                      M.get_name (| globals, "base_length" |);
                      M.get_name (| globals, "modulus_length" |)
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |),
          M.call (|
            M.get_name (| globals, "max" |),
            make_list [
              M.get_name (| globals, "adjusted_exp_length" |);
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
        |),
        M.get_name (| globals, "GQUADDIVISOR" |)
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

Definition get_mult_complexity : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "x" ] |) in
    let _ := Constant.str "
    Estimate the complexity of performing Karatsuba multiplication.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.get_name (| globals, "x" |),
          Constant.int 64
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          BinOp.pow (|
            M.get_name (| globals, "x" |),
            Constant.int 2
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt_e (|
              M.get_name (| globals, "x" |),
              Constant.int 1024
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              BinOp.sub (|
                BinOp.add (|
                  BinOp.floor_div (|
                    BinOp.pow (|
                      M.get_name (| globals, "x" |),
                      Constant.int 2
                    |),
                    Constant.int 4
                  |),
                  BinOp.mult (|
                    Constant.int 96,
                    M.get_name (| globals, "x" |)
                  |)
                |),
                Constant.int 3072
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.return_ (|
              BinOp.sub (|
                BinOp.add (|
                  BinOp.floor_div (|
                    BinOp.pow (|
                      M.get_name (| globals, "x" |),
                      Constant.int 2
                    |),
                    Constant.int 16
                  |),
                  BinOp.mult (|
                    Constant.int 480,
                    M.get_name (| globals, "x" |)
                  |)
                |),
                Constant.int 199680
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).
