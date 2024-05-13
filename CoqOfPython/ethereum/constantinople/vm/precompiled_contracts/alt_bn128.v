Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.constantinople.vm.precompiled_contracts.alt_bn128".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) ALT_BN128 CONTRACTS
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the ALT_BN128 precompiled contracts.
".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_crypto_alt_bn128_imports_ALT_BN128_CURVE_ORDER :
  IsImported globals "ethereum.crypto.alt_bn128" "ALT_BN128_CURVE_ORDER".
Axiom ethereum_crypto_alt_bn128_imports_ALT_BN128_PRIME :
  IsImported globals "ethereum.crypto.alt_bn128" "ALT_BN128_PRIME".
Axiom ethereum_crypto_alt_bn128_imports_BNF :
  IsImported globals "ethereum.crypto.alt_bn128" "BNF".
Axiom ethereum_crypto_alt_bn128_imports_BNF2 :
  IsImported globals "ethereum.crypto.alt_bn128" "BNF2".
Axiom ethereum_crypto_alt_bn128_imports_BNF12 :
  IsImported globals "ethereum.crypto.alt_bn128" "BNF12".
Axiom ethereum_crypto_alt_bn128_imports_BNP :
  IsImported globals "ethereum.crypto.alt_bn128" "BNP".
Axiom ethereum_crypto_alt_bn128_imports_BNP2 :
  IsImported globals "ethereum.crypto.alt_bn128" "BNP2".
Axiom ethereum_crypto_alt_bn128_imports_pairing :
  IsImported globals "ethereum.crypto.alt_bn128" "pairing".

Axiom ethereum_utils_ensure_imports_ensure :
  IsImported globals "ethereum.utils.ensure" "ensure".

Axiom ethereum_constantinople_vm_imports_Evm :
  IsImported globals "ethereum.constantinople.vm" "Evm".

Axiom ethereum_constantinople_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.constantinople.vm.gas" "charge_gas".

Axiom ethereum_constantinople_vm_memory_imports_buffer_read :
  IsImported globals "ethereum.constantinople.vm.memory" "buffer_read".

Axiom ethereum_constantinople_vm_exceptions_imports_OutOfGasError :
  IsImported globals "ethereum.constantinople.vm.exceptions" "OutOfGasError".

Definition alt_bn128_add : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    The ALT_BN128 addition precompiled contract.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          Constant.int 500
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "x0_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "x0_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "x0_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y0_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "y0_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "y0_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "x1_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "x1_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "x1_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y1_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "y1_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "y1_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "i" |),
        make_tuple [ M.get_name (| globals, locals_stack, "x0_value" |); M.get_name (| globals, locals_stack, "y0_value" |); M.get_name (| globals, locals_stack, "x1_value" |); M.get_name (| globals, locals_stack, "y1_value" |) ],
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt_e (|
                M.get_name (| globals, locals_stack, "i" |),
                M.get_name (| globals, locals_stack, "ALT_BN128_PRIME" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "OutOfGasError" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
(* At stmt: unsupported node type: Try *)
    let _ := M.assign_local (|
      "p" ,
      BinOp.add (|
        M.get_name (| globals, locals_stack, "p0" |),
        M.get_name (| globals, locals_stack, "p1" |)
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
      BinOp.add (|
        M.call (|
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "p" |), "x" |), "to_be_bytes32" |),
          make_list [],
          make_dict []
        |),
        M.call (|
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "p" |), "y" |), "to_be_bytes32" |),
          make_list [],
          make_dict []
        |)
      |)
    |) in
    M.pure Constant.None_)).

Definition alt_bn128_mul : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    The ALT_BN128 multiplication precompiled contract.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          Constant.int 40000
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "x0_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "x0_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "x0_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y0_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "y0_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "y0_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "n" ,
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
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "i" |),
        make_tuple [ M.get_name (| globals, locals_stack, "x0_value" |); M.get_name (| globals, locals_stack, "y0_value" |) ],
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt_e (|
                M.get_name (| globals, locals_stack, "i" |),
                M.get_name (| globals, locals_stack, "ALT_BN128_PRIME" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "OutOfGasError" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
(* At stmt: unsupported node type: Try *)
    let _ := M.assign_local (|
      "p" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "p0" |), "mul_by" |),
        make_list [
          M.get_name (| globals, locals_stack, "n" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
      BinOp.add (|
        M.call (|
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "p" |), "x" |), "to_be_bytes32" |),
          make_list [],
          make_dict []
        |),
        M.call (|
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "p" |), "y" |), "to_be_bytes32" |),
          make_list [],
          make_dict []
        |)
      |)
    |) in
    M.pure Constant.None_)).

Definition alt_bn128_pairing_check : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    The ALT_BN128 pairing check precompiled contract.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          BinOp.add (|
            BinOp.mult (|
              Constant.int 80000,
              BinOp.floor_div (|
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "data" |)
                  ],
                  make_dict []
                |),
                Constant.int 192
              |)
            |),
            Constant.int 100000
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
        Compare.not_eq (|
          BinOp.mod_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                M.get_name (| globals, locals_stack, "data" |)
              ],
              make_dict []
            |),
            Constant.int 192
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "OutOfGasError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "result" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
        make_list [
          Constant.int 1
        ],
        make_dict []
      |)
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "i" |),
        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        BinOp.floor_div (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "data" |)
            ],
            make_dict []
          |),
          Constant.int 192
        |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "values" ,
            make_list []
          |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, locals_stack, "j" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        Constant.int 6
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.assign_local (|
                  "value" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
                    make_list [
                      M.slice (|
                        M.get_name (| globals, locals_stack, "data" |),
                        BinOp.add (|
                          BinOp.mult (|
                            M.get_name (| globals, locals_stack, "i" |),
                            Constant.int 192
                          |),
                          BinOp.mult (|
                            Constant.int 32,
                            M.get_name (| globals, locals_stack, "j" |)
                          |)
                        |),
                        BinOp.add (|
                          BinOp.mult (|
                            M.get_name (| globals, locals_stack, "i" |),
                            Constant.int 192
                          |),
                          BinOp.mult (|
                            Constant.int 32,
                            BinOp.add (|
                              M.get_name (| globals, locals_stack, "j" |),
                              Constant.int 1
                            |)
                          |)
                        |),
                        Constant.None_
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.gt_e (|
                      M.get_name (| globals, locals_stack, "value" |),
                      M.get_name (| globals, locals_stack, "ALT_BN128_PRIME" |)
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "OutOfGasError" |)) |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    M.pure Constant.None_
                  )) |) in
                let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "values" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, locals_stack, "int" |),
        make_list [
          M.get_name (| globals, locals_stack, "value" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
                M.pure Constant.None_
              )),
              ltac:(M.monadic (
                M.pure Constant.None_
              ))
          |) in
(* At stmt: unsupported node type: Try *)
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "p" |), "mul_by" |),
          make_list [
            M.get_name (| globals, locals_stack, "ALT_BN128_CURVE_ORDER" |)
          ],
          make_dict []
        |),
        M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "BNP" |), "point_at_infinity" |),
          make_list [],
          make_dict []
        |)
      |);
      M.get_name (| globals, locals_stack, "OutOfGasError" |)
    ],
    make_dict []
  |) in
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "q" |), "mul_by" |),
          make_list [
            M.get_name (| globals, locals_stack, "ALT_BN128_CURVE_ORDER" |)
          ],
          make_dict []
        |),
        M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "BNP2" |), "point_at_infinity" |),
          make_list [],
          make_dict []
        |)
      |);
      M.get_name (| globals, locals_stack, "OutOfGasError" |)
    ],
    make_dict []
  |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.and (|
                Compare.not_eq (|
                  M.get_name (| globals, locals_stack, "p" |),
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "BNP" |), "point_at_infinity" |),
                    make_list [],
                    make_dict []
                  |)
                |),
                ltac:(M.monadic (
                  Compare.not_eq (|
                    M.get_name (| globals, locals_stack, "q" |),
                    M.call (|
                      M.get_field (| M.get_name (| globals, locals_stack, "BNP2" |), "point_at_infinity" |),
                      make_list [],
                      make_dict []
                    |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.assign_local (|
                "result" ,
                BinOp.mult (|
                  M.get_name (| globals, locals_stack, "result" |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "pairing" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "q" |);
                      M.get_name (| globals, locals_stack, "p" |)
                    ],
                    make_dict []
                  |)
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "result" |),
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
            make_list [
              Constant.int 1
            ],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
          M.call (|
            M.get_field (| M.call (|
              M.get_name (| globals, locals_stack, "U256" |),
              make_list [
                Constant.int 1
              ],
              make_dict []
            |), "to_be_bytes32" |),
            make_list [],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "output" |),
          M.call (|
            M.get_field (| M.call (|
              M.get_name (| globals, locals_stack, "U256" |),
              make_list [
                Constant.int 0
              ],
              make_dict []
            |), "to_be_bytes32" |),
            make_list [],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).
