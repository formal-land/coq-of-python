Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Arithmetic Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM Arithmetic instructions.
".

Require ethereum.base_types.
Axiom ethereum_base_types_U255_CEIL_VALUE :
  IsGlobalAlias globals ethereum.base_types.globals "U255_CEIL_VALUE".
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_U256_CEIL_VALUE :
  IsGlobalAlias globals ethereum.base_types.globals "U256_CEIL_VALUE".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.utils.numeric.
Axiom ethereum_utils_numeric_get_sign :
  IsGlobalAlias globals ethereum.utils.numeric.globals "get_sign".

Require ethereum.london.vm.__init__.
Axiom ethereum_london_vm___init___Evm :
  IsGlobalAlias globals ethereum.london.vm.__init__.globals "Evm".

Require ethereum.london.vm.gas.
Axiom ethereum_london_vm_gas_GAS_EXPONENTIATION :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_EXPONENTIATION".
Axiom ethereum_london_vm_gas_GAS_EXPONENTIATION_PER_BYTE :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_EXPONENTIATION_PER_BYTE".
Axiom ethereum_london_vm_gas_GAS_LOW :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_LOW".
Axiom ethereum_london_vm_gas_GAS_MID :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_MID".
Axiom ethereum_london_vm_gas_GAS_VERY_LOW :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "GAS_VERY_LOW".
Axiom ethereum_london_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.london.vm.gas.globals "charge_gas".

Require ethereum.london.vm.stack.
Axiom ethereum_london_vm_stack_pop :
  IsGlobalAlias globals ethereum.london.vm.stack.globals "pop".
Axiom ethereum_london_vm_stack_push :
  IsGlobalAlias globals ethereum.london.vm.stack.globals "push".

Definition add : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Adds the top two elements of the stack together, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let x :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let y :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let result :=
      M.call (|
        M.get_field (| M.get_name (| globals, "x" |), "wrapping_add" |),
        make_list [
          M.get_name (| globals, "y" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition sub : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Subtracts the top two elements of the stack, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let x :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let y :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let result :=
      M.call (|
        M.get_field (| M.get_name (| globals, "x" |), "wrapping_sub" |),
        make_list [
          M.get_name (| globals, "y" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition mul : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Multiply the top two elements of the stack, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let x :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let y :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let result :=
      M.call (|
        M.get_field (| M.get_name (| globals, "x" |), "wrapping_mul" |),
        make_list [
          M.get_name (| globals, "y" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition div : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Integer division of the top two elements of the stack. Pushes the result
    back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let dividend :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let divisor :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "divisor" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let quotient :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let quotient :=
          BinOp.floor_div (|
            M.get_name (| globals, "dividend" |),
            M.get_name (| globals, "divisor" |)
          |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "quotient" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition sdiv : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Signed integer division of the top two elements of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let dividend :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_signed" |),
        make_list [],
        make_dict []
      |) in
    let divisor :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_signed" |),
        make_list [],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "divisor" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let quotient :=
          Constant.int 0 in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              Compare.eq (|
                M.get_name (| globals, "dividend" |),
                UnOp.sub (| M.get_name (| globals, "U255_CEIL_VALUE" |) |)
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_name (| globals, "divisor" |),
                  UnOp.sub (| Constant.int 1 |)
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let quotient :=
              UnOp.sub (| M.get_name (| globals, "U255_CEIL_VALUE" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let sign :=
              M.call (|
                M.get_name (| globals, "get_sign" |),
                make_list [
                  BinOp.mult (|
                    M.get_name (| globals, "dividend" |),
                    M.get_name (| globals, "divisor" |)
                  |)
                ],
                make_dict []
              |) in
            let quotient :=
              BinOp.mult (|
                M.get_name (| globals, "sign" |),
                BinOp.floor_div (|
                  M.call (|
                    M.get_name (| globals, "abs" |),
                    make_list [
                      M.get_name (| globals, "dividend" |)
                    ],
                    make_dict []
                  |),
                  M.call (|
                    M.get_name (| globals, "abs" |),
                    make_list [
                      M.get_name (| globals, "divisor" |)
                    ],
                    make_dict []
                  |)
                |)
              |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_signed" |),
        make_list [
          M.get_name (| globals, "quotient" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition mod : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Modulo remainder of the top two elements of the stack. Pushes the result
    back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let x :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let y :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "y" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let remainder :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let remainder :=
          BinOp.mod_ (|
            M.get_name (| globals, "x" |),
            M.get_name (| globals, "y" |)
          |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "remainder" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition smod : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Signed modulo remainder of the top two elements of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let x :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_signed" |),
        make_list [],
        make_dict []
      |) in
    let y :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_signed" |),
        make_list [],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "y" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let remainder :=
          Constant.int 0 in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let remainder :=
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, "get_sign" |),
              make_list [
                M.get_name (| globals, "x" |)
              ],
              make_dict []
            |),
            BinOp.mod_ (|
              M.call (|
                M.get_name (| globals, "abs" |),
                make_list [
                  M.get_name (| globals, "x" |)
                ],
                make_dict []
              |),
              M.call (|
                M.get_name (| globals, "abs" |),
                make_list [
                  M.get_name (| globals, "y" |)
                ],
                make_dict []
              |)
            |)
          |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.call (|
        M.get_field (| M.get_name (| globals, "U256" |), "from_signed" |),
        make_list [
          M.get_name (| globals, "remainder" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition addmod : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Modulo addition of the top 2 elements with the 3rd element. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let x :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let y :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let z :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
      M.get_name (| globals, "GAS_MID" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "z" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let result :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let result :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              BinOp.mod_ (|
                BinOp.add (|
                  M.get_name (| globals, "x" |),
                  M.get_name (| globals, "y" |)
                |),
                M.get_name (| globals, "z" |)
              |)
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition mulmod : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Modulo multiplication of the top 2 elements with the 3rd element. Pushes
    the result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let x :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let y :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let z :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
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
      M.get_name (| globals, "GAS_MID" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "z" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let result :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let result :=
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              BinOp.mod_ (|
                BinOp.mult (|
                  M.get_name (| globals, "x" |),
                  M.get_name (| globals, "y" |)
                |),
                M.get_name (| globals, "z" |)
              |)
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition exp : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Exponential operation of the top 2 elements. Pushes the result back on
    the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let base :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let exponent :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let exponent_bits :=
      M.call (|
        M.get_field (| M.get_name (| globals, "exponent" |), "bit_length" |),
        make_list [],
        make_dict []
      |) in
    let exponent_bytes :=
      BinOp.floor_div (|
        BinOp.add (|
          M.get_name (| globals, "exponent_bits" |),
          Constant.int 7
        |),
        Constant.int 8
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.add (|
        M.get_name (| globals, "GAS_EXPONENTIATION" |),
        BinOp.mult (|
          M.get_name (| globals, "GAS_EXPONENTIATION_PER_BYTE" |),
          M.get_name (| globals, "exponent_bytes" |)
        |)
      |)
    ],
    make_dict []
  |) in
    let result :=
      M.call (|
        M.get_name (| globals, "U256" |),
        make_list [
          M.call (|
            M.get_name (| globals, "pow" |),
            make_list [
              M.get_name (| globals, "base" |);
              M.get_name (| globals, "exponent" |);
              M.get_name (| globals, "U256_CEIL_VALUE" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Definition signextend : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Sign extend operation. In other words, extend a signed number which
    fits in N bytes to 32 bytes.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let byte_num :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let value :=
      M.call (|
        M.get_name (| globals, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, "evm" |), "stack" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      M.get_name (| globals, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.get_name (| globals, "byte_num" |),
          Constant.int 31
        |),
      (* then *)
      ltac:(M.monadic (
        let result :=
          M.get_name (| globals, "value" |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let value_bytes :=
          M.call (|
            M.get_name (| globals, "bytes" |),
            make_list [
              M.call (|
                M.get_field (| M.get_name (| globals, "value" |), "to_be_bytes32" |),
                make_list [],
                make_dict []
              |)
            ],
            make_dict []
          |) in
        let value_bytes :=
          M.get_subscript (| M.get_name (| globals, "value_bytes" |), M.slice (| BinOp.sub (|
            Constant.int 31,
            M.call (|
              M.get_name (| globals, "int" |),
              make_list [
                M.get_name (| globals, "byte_num" |)
              ],
              make_dict []
            |)
          |), Constant.None_ |) |) in
        let sign_bit :=
          BinOp.r_shift (|
            M.get_subscript (| M.get_name (| globals, "value_bytes" |), Constant.int 0 |),
            Constant.int 7
          |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_name (| globals, "sign_bit" |),
              Constant.int 0
            |),
          (* then *)
          ltac:(M.monadic (
            let result :=
              M.call (|
                M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
                make_list [
                  M.get_name (| globals, "value_bytes" |)
                ],
                make_dict []
              |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let num_bytes_prepend :=
              BinOp.sub (|
                Constant.int 32,
                BinOp.add (|
                  M.get_name (| globals, "byte_num" |),
                  Constant.int 1
                |)
              |) in
            let result :=
              M.call (|
                M.get_field (| M.get_name (| globals, "U256" |), "from_be_bytes" |),
                make_list [
                  BinOp.add (|
                    M.call (|
                      M.get_name (| globals, "bytearray" |),
                      make_list [
                        BinOp.mult (|
                          make_list [
                            Constant.int 255
                          ],
                          M.get_name (| globals, "num_bytes_prepend" |)
                        |)
                      ],
                      make_dict []
                    |),
                    M.get_name (| globals, "value_bytes" |)
                  |)
                ],
                make_dict []
              |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, "evm" |), "stack" |);
      M.get_name (| globals, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).
