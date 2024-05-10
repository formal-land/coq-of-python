Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.byzantium.vm.precompiled_contracts.alt_bn128".

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

Axiom ethereum_byzantium_vm_imports_Evm :
  IsImported globals "ethereum.byzantium.vm" "Evm".

Axiom ethereum_byzantium_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.byzantium.vm.gas" "charge_gas".

Axiom ethereum_byzantium_vm_memory_imports_buffer_read :
  IsImported globals "ethereum.byzantium.vm.memory" "buffer_read".

Axiom ethereum_byzantium_vm_exceptions_imports_OutOfGasError :
  IsImported globals "ethereum.byzantium.vm.exceptions" "OutOfGasError".

Definition alt_bn128_add : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    The ALT_BN128 addition precompiled contract.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.call (|
        M.get_name (| globals, "Uint" |),
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
    |) in
    let _ := M.assign_local (|
      "x0_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "x0_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y0_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "y0_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "y0_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "x1_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "x1_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "x1_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y1_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "y1_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "y1_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, "i" |),
        make_tuple [ M.get_name (| globals, "x0_value" |); M.get_name (| globals, "y0_value" |); M.get_name (| globals, "x1_value" |); M.get_name (| globals, "y1_value" |) ],
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt_e (|
                M.get_name (| globals, "i" |),
                M.get_name (| globals, "ALT_BN128_PRIME" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, "OutOfGasError" |)) |) in
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
        M.get_name (| globals, "p0" |),
        M.get_name (| globals, "p1" |)
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      BinOp.add (|
        M.call (|
          M.get_field (| M.get_field (| M.get_name (| globals, "p" |), "x" |), "to_be_bytes32" |),
          make_list [],
          make_dict []
        |),
        M.call (|
          M.get_field (| M.get_field (| M.get_name (| globals, "p" |), "y" |), "to_be_bytes32" |),
          make_list [],
          make_dict []
        |)
      |)
    |) in
    M.pure Constant.None_)).

Definition alt_bn128_mul : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    The ALT_BN128 multiplication precompiled contract.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.call (|
        M.get_name (| globals, "Uint" |),
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
    |) in
    let _ := M.assign_local (|
      "x0_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "x0_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y0_bytes" ,
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
    |) in
    let _ := M.assign_local (|
      "y0_value" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "y0_bytes" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "n" ,
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
      |)
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, "i" |),
        make_tuple [ M.get_name (| globals, "x0_value" |); M.get_name (| globals, "y0_value" |) ],
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt_e (|
                M.get_name (| globals, "i" |),
                M.get_name (| globals, "ALT_BN128_PRIME" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, "OutOfGasError" |)) |) in
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
        M.get_field (| M.get_name (| globals, "p0" |), "mul_by" |),
        make_list [
          M.get_name (| globals, "n" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      BinOp.add (|
        M.call (|
          M.get_field (| M.get_field (| M.get_name (| globals, "p" |), "x" |), "to_be_bytes32" |),
          make_list [],
          make_dict []
        |),
        M.call (|
          M.get_field (| M.get_field (| M.get_name (| globals, "p" |), "y" |), "to_be_bytes32" |),
          make_list [],
          make_dict []
        |)
      |)
    |) in
    M.pure Constant.None_)).

Definition alt_bn128_pairing_check : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    The ALT_BN128 pairing check precompiled contract.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let _ := M.assign_local (|
      "data" ,
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          BinOp.add (|
            BinOp.mult (|
              Constant.int 80000,
              BinOp.floor_div (|
                M.call (|
                  M.get_name (| globals, "len" |),
                  make_list [
                    M.get_name (| globals, "data" |)
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
              M.get_name (| globals, "len" |),
              make_list [
                M.get_name (| globals, "data" |)
              ],
              make_dict []
            |),
            Constant.int 192
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, "OutOfGasError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "result" ,
      M.call (|
        M.get_field (| M.get_name (| globals, "BNF12" |), "from_int" |),
        make_list [
          Constant.int 1
        ],
        make_dict []
      |)
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, "i" |),
        M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        BinOp.floor_div (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "data" |)
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
              M.get_name (| globals, "j" |),
              M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        Constant.int 6
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.assign_local (|
                  "value" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
                    make_list [
                      M.slice (|
                        M.get_name (| globals, "data" |),
                        BinOp.add (|
                          BinOp.mult (|
                            M.get_name (| globals, "i" |),
                            Constant.int 192
                          |),
                          BinOp.mult (|
                            Constant.int 32,
                            M.get_name (| globals, "j" |)
                          |)
                        |),
                        BinOp.add (|
                          BinOp.mult (|
                            M.get_name (| globals, "i" |),
                            Constant.int 192
                          |),
                          BinOp.mult (|
                            Constant.int 32,
                            BinOp.add (|
                              M.get_name (| globals, "j" |),
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
                      M.get_name (| globals, "value" |),
                      M.get_name (| globals, "ALT_BN128_PRIME" |)
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.raise (| Some (M.get_name (| globals, "OutOfGasError" |)) |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    M.pure Constant.None_
                  )) |) in
                let _ := M.call (|
    M.get_field (| M.get_name (| globals, "values" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, "int" |),
        make_list [
          M.get_name (| globals, "value" |)
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
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_field (| M.get_name (| globals, "p" |), "mul_by" |),
          make_list [
            M.get_name (| globals, "ALT_BN128_CURVE_ORDER" |)
          ],
          make_dict []
        |),
        M.call (|
          M.get_field (| M.get_name (| globals, "BNP" |), "point_at_infinity" |),
          make_list [],
          make_dict []
        |)
      |);
      M.get_name (| globals, "OutOfGasError" |)
    ],
    make_dict []
  |) in
          let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_field (| M.get_name (| globals, "q" |), "mul_by" |),
          make_list [
            M.get_name (| globals, "ALT_BN128_CURVE_ORDER" |)
          ],
          make_dict []
        |),
        M.call (|
          M.get_field (| M.get_name (| globals, "BNP2" |), "point_at_infinity" |),
          make_list [],
          make_dict []
        |)
      |);
      M.get_name (| globals, "OutOfGasError" |)
    ],
    make_dict []
  |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.and (|
                Compare.not_eq (|
                  M.get_name (| globals, "p" |),
                  M.call (|
                    M.get_field (| M.get_name (| globals, "BNP" |), "point_at_infinity" |),
                    make_list [],
                    make_dict []
                  |)
                |),
                ltac:(M.monadic (
                  Compare.not_eq (|
                    M.get_name (| globals, "q" |),
                    M.call (|
                      M.get_field (| M.get_name (| globals, "BNP2" |), "point_at_infinity" |),
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
                  M.get_name (| globals, "result" |),
                  M.call (|
                    M.get_name (| globals, "pairing" |),
                    make_list [
                      M.get_name (| globals, "q" |);
                      M.get_name (| globals, "p" |)
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
          M.get_name (| globals, "result" |),
          M.call (|
            M.get_field (| M.get_name (| globals, "BNF12" |), "from_int" |),
            make_list [
              Constant.int 1
            ],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, "evm" |), "output" |),
          M.call (|
            M.get_field (| M.call (|
              M.get_name (| globals, "U256" |),
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
          M.get_field (| M.get_name (| globals, "evm" |), "output" |),
          M.call (|
            M.get_field (| M.call (|
              M.get_name (| globals, "U256" |),
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
