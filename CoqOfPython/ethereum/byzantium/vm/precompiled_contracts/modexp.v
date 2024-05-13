Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.byzantium.vm.precompiled_contracts.modexp".

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

Axiom ethereum_byzantium_vm_imports_Evm :
  IsImported globals "ethereum.byzantium.vm" "Evm".

Axiom ethereum_byzantium_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.byzantium.vm.gas" "charge_gas".

Axiom ethereum_byzantium_vm_memory_imports_buffer_read :
  IsImported globals "ethereum.byzantium.vm.memory" "buffer_read".

Definition GQUADDIVISOR : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 20
    ],
    make_dict []
  |)
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
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
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
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, locals_stack, "exp_length" |),
          Constant.int 32
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "adjusted_exp_length" ,
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "max" |),
                make_list [
                  Constant.int 0;
                  BinOp.sub (|
                    M.call (|
                      M.get_field (| M.get_name (| globals, locals_stack, "exp_head" |), "bit_length" |),
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
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "adjusted_exp_length" ,
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              BinOp.add (|
                BinOp.mult (|
                  Constant.int 8,
                  BinOp.sub (|
                    M.call (|
                      M.get_name (| globals, locals_stack, "int" |),
                      make_list [
                        M.get_name (| globals, locals_stack, "exp_length" |)
                      ],
                      make_dict []
                    |),
                    Constant.int 32
                  |)
                |),
                M.call (|
                  M.get_name (| globals, locals_stack, "max" |),
                  make_list [
                    Constant.int 0;
                    BinOp.sub (|
                      M.call (|
                        M.get_field (| M.get_name (| globals, locals_stack, "exp_head" |), "bit_length" |),
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
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.floor_div (|
        BinOp.mult (|
          M.call (|
            M.get_name (| globals, locals_stack, "get_mult_complexity" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  M.call (|
                    M.get_name (| globals, locals_stack, "max" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "base_length" |);
                      M.get_name (| globals, locals_stack, "modulus_length" |)
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
            M.get_name (| globals, locals_stack, "max" |),
            make_list [
              M.get_name (| globals, locals_stack, "adjusted_exp_length" |);
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
        |),
        M.get_name (| globals, locals_stack, "GQUADDIVISOR" |)
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

Definition get_mult_complexity : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "x" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Estimate the complexity of performing Karatsuba multiplication.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.get_name (| globals, locals_stack, "x" |),
          Constant.int 64
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          BinOp.pow (|
            M.get_name (| globals, locals_stack, "x" |),
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
              M.get_name (| globals, locals_stack, "x" |),
              Constant.int 1024
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              BinOp.sub (|
                BinOp.add (|
                  BinOp.floor_div (|
                    BinOp.pow (|
                      M.get_name (| globals, locals_stack, "x" |),
                      Constant.int 2
                    |),
                    Constant.int 4
                  |),
                  BinOp.mult (|
                    Constant.int 96,
                    M.get_name (| globals, locals_stack, "x" |)
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
                      M.get_name (| globals, locals_stack, "x" |),
                      Constant.int 2
                    |),
                    Constant.int 16
                  |),
                  BinOp.mult (|
                    Constant.int 480,
                    M.get_name (| globals, locals_stack, "x" |)
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

Axiom get_mult_complexity_in_globals :
  IsInGlobals globals "get_mult_complexity" (make_function get_mult_complexity).
