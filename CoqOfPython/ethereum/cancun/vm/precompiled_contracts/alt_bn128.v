Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.crypto.alt_bn128.
Axiom ethereum_crypto_alt_bn128_ALT_BN128_CURVE_ORDER :
  IsGlobalAlias globals ethereum.crypto.alt_bn128.globals "ALT_BN128_CURVE_ORDER".
Axiom ethereum_crypto_alt_bn128_ALT_BN128_PRIME :
  IsGlobalAlias globals ethereum.crypto.alt_bn128.globals "ALT_BN128_PRIME".
Axiom ethereum_crypto_alt_bn128_BNF :
  IsGlobalAlias globals ethereum.crypto.alt_bn128.globals "BNF".
Axiom ethereum_crypto_alt_bn128_BNF2 :
  IsGlobalAlias globals ethereum.crypto.alt_bn128.globals "BNF2".
Axiom ethereum_crypto_alt_bn128_BNF12 :
  IsGlobalAlias globals ethereum.crypto.alt_bn128.globals "BNF12".
Axiom ethereum_crypto_alt_bn128_BNP :
  IsGlobalAlias globals ethereum.crypto.alt_bn128.globals "BNP".
Axiom ethereum_crypto_alt_bn128_BNP2 :
  IsGlobalAlias globals ethereum.crypto.alt_bn128.globals "BNP2".
Axiom ethereum_crypto_alt_bn128_pairing :
  IsGlobalAlias globals ethereum.crypto.alt_bn128.globals "pairing".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require ethereum.cancun.vm.__init__.
Axiom ethereum_cancun_vm___init___Evm :
  IsGlobalAlias globals ethereum.cancun.vm.__init__.globals "Evm".

Require ethereum.cancun.vm.gas.
Axiom ethereum_cancun_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.cancun.vm.gas.globals "charge_gas".

Require ethereum.cancun.vm.memory.
Axiom ethereum_cancun_vm_memory_buffer_read :
  IsGlobalAlias globals ethereum.cancun.vm.memory.globals "buffer_read".

Require ethereum.cancun.vm.exceptions.
Axiom ethereum_cancun_vm_exceptions_OutOfGasError :
  IsGlobalAlias globals ethereum.cancun.vm.exceptions.globals "OutOfGasError".

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
    let data :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 150
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let x0_bytes :=
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
      |) in
    let x0_value :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "x0_bytes" |)
        ],
        make_dict []
      |) in
    let y0_bytes :=
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
      |) in
    let y0_value :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "y0_bytes" |)
        ],
        make_dict []
      |) in
    let x1_bytes :=
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
      |) in
    let x1_value :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "x1_bytes" |)
        ],
        make_dict []
      |) in
    let y1_bytes :=
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
      |) in
    let y1_value :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "y1_bytes" |)
        ],
        make_dict []
      |) in
    For M.get_name (| globals, "i" |) in make_tuple [ M.get_name (| globals, "x0_value" |); M.get_name (| globals, "y0_value" |); M.get_name (| globals, "x1_value" |); M.get_name (| globals, "y1_value" |) ] do
      let _ :=
        (* if *)
        M.if_then_else (|
          Compare.gt_e (|
            M.get_name (| globals, "i" |),
            M.get_name (| globals, "ALT_BN128_PRIME" |)
          |),
        (* then *)
        ltac:(M.monadic (
          let _ := M.raise (| Some(M.get_name (| globals, "OutOfGasError" |)) |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          M.pure Constant.None_
        )) |) in
    EndFor.
(* At stmt: unsupported node type: Try *)
    let p :=
      BinOp.add (|
        M.get_name (| globals, "p0" |),
        M.get_name (| globals, "p1" |)
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
    let data :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 6000
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let x0_bytes :=
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
      |) in
    let x0_value :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "x0_bytes" |)
        ],
        make_dict []
      |) in
    let y0_bytes :=
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
      |) in
    let y0_value :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
        make_list [
          M.get_name (| globals, "y0_bytes" |)
        ],
        make_dict []
      |) in
    let n :=
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
    For M.get_name (| globals, "i" |) in make_tuple [ M.get_name (| globals, "x0_value" |); M.get_name (| globals, "y0_value" |) ] do
      let _ :=
        (* if *)
        M.if_then_else (|
          Compare.gt_e (|
            M.get_name (| globals, "i" |),
            M.get_name (| globals, "ALT_BN128_PRIME" |)
          |),
        (* then *)
        ltac:(M.monadic (
          let _ := M.raise (| Some(M.get_name (| globals, "OutOfGasError" |)) |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          M.pure Constant.None_
        )) |) in
    EndFor.
(* At stmt: unsupported node type: Try *)
    let p :=
      M.call (|
        M.get_field (| M.get_name (| globals, "p0" |), "mul_by" |),
        make_list [
          M.get_name (| globals, "n" |)
        ],
        make_dict []
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
    let data :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          BinOp.add (|
            BinOp.mult (|
              Constant.int 34000,
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
            Constant.int 45000
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
        let _ := M.raise (| Some(M.get_name (| globals, "OutOfGasError" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let result :=
      M.call (|
        M.get_field (| M.get_name (| globals, "BNF12" |), "from_int" |),
        make_list [
          Constant.int 1
        ],
        make_dict []
      |) in
    For M.get_name (| globals, "i" |) in M.call (|
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
  |) do
      let values :=
        make_list [] in
      For M.get_name (| globals, "j" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      Constant.int 6
    ],
    make_dict []
  |) do
        let value :=
          M.call (|
            M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
            make_list [
              M.get_subscript (| M.get_name (| globals, "data" |), M.slice (| BinOp.add (|
                BinOp.mult (|
                  M.get_name (| globals, "i" |),
                  Constant.int 192
                |),
                BinOp.mult (|
                  Constant.int 32,
                  M.get_name (| globals, "j" |)
                |)
              |), BinOp.add (|
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
              |) |) |)
            ],
            make_dict []
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
            let _ := M.raise (| Some(M.get_name (| globals, "OutOfGasError" |)) |) in
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
      EndFor.
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
          let result :=
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
            |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          M.pure Constant.None_
        )) |) in
    EndFor.
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
