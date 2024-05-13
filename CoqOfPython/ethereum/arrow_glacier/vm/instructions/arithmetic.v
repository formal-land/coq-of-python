Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.arrow_glacier.vm.instructions.arithmetic".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_base_types_imports_U255_CEIL_VALUE :
  IsImported globals "ethereum.base_types" "U255_CEIL_VALUE".
Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_U256_CEIL_VALUE :
  IsImported globals "ethereum.base_types" "U256_CEIL_VALUE".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_utils_numeric_imports_get_sign :
  IsImported globals "ethereum.utils.numeric" "get_sign".

Axiom ethereum_arrow_glacier_vm_imports_Evm :
  IsImported globals "ethereum.arrow_glacier.vm" "Evm".

Axiom ethereum_arrow_glacier_vm_gas_imports_GAS_EXPONENTIATION :
  IsImported globals "ethereum.arrow_glacier.vm.gas" "GAS_EXPONENTIATION".
Axiom ethereum_arrow_glacier_vm_gas_imports_GAS_EXPONENTIATION_PER_BYTE :
  IsImported globals "ethereum.arrow_glacier.vm.gas" "GAS_EXPONENTIATION_PER_BYTE".
Axiom ethereum_arrow_glacier_vm_gas_imports_GAS_LOW :
  IsImported globals "ethereum.arrow_glacier.vm.gas" "GAS_LOW".
Axiom ethereum_arrow_glacier_vm_gas_imports_GAS_MID :
  IsImported globals "ethereum.arrow_glacier.vm.gas" "GAS_MID".
Axiom ethereum_arrow_glacier_vm_gas_imports_GAS_VERY_LOW :
  IsImported globals "ethereum.arrow_glacier.vm.gas" "GAS_VERY_LOW".
Axiom ethereum_arrow_glacier_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.arrow_glacier.vm.gas" "charge_gas".

Axiom ethereum_arrow_glacier_vm_stack_imports_pop :
  IsImported globals "ethereum.arrow_glacier.vm.stack" "pop".
Axiom ethereum_arrow_glacier_vm_stack_imports_push :
  IsImported globals "ethereum.arrow_glacier.vm.stack" "push".

Definition add : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Adds the top two elements of the stack together, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "x" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "result" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "x" |), "wrapping_add" |),
        make_list [
          M.get_name (| globals, locals_stack, "y" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom add_in_globals :
  IsInGlobals globals "add" (make_function add).

Definition sub : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Subtracts the top two elements of the stack, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "x" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "result" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "x" |), "wrapping_sub" |),
        make_list [
          M.get_name (| globals, locals_stack, "y" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom sub_in_globals :
  IsInGlobals globals "sub" (make_function sub).

Definition mul : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Multiply the top two elements of the stack, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "x" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "result" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "x" |), "wrapping_mul" |),
        make_list [
          M.get_name (| globals, locals_stack, "y" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom mul_in_globals :
  IsInGlobals globals "mul" (make_function mul).

Definition div : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Integer division of the top two elements of the stack. Pushes the result
    back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "dividend" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "divisor" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "divisor" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "quotient" ,
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "quotient" ,
          BinOp.floor_div (|
            M.get_name (| globals, locals_stack, "dividend" |),
            M.get_name (| globals, locals_stack, "divisor" |)
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "quotient" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom div_in_globals :
  IsInGlobals globals "div" (make_function div).

Definition sdiv : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Signed integer division of the top two elements of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "dividend" ,
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_signed" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "divisor" ,
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_signed" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "divisor" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "quotient" ,
          Constant.int 0
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              Compare.eq (|
                M.get_name (| globals, locals_stack, "dividend" |),
                UnOp.sub (| M.get_name (| globals, locals_stack, "U255_CEIL_VALUE" |) |)
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_name (| globals, locals_stack, "divisor" |),
                  UnOp.sub (| Constant.int 1 |)
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "quotient" ,
              UnOp.sub (| M.get_name (| globals, locals_stack, "U255_CEIL_VALUE" |) |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "sign" ,
              M.call (|
                M.get_name (| globals, locals_stack, "get_sign" |),
                make_list [
                  BinOp.mult (|
                    M.get_name (| globals, locals_stack, "dividend" |),
                    M.get_name (| globals, locals_stack, "divisor" |)
                  |)
                ],
                make_dict []
              |)
            |) in
            let _ := M.assign_local (|
              "quotient" ,
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "sign" |),
                BinOp.floor_div (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "abs" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "dividend" |)
                    ],
                    make_dict []
                  |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "abs" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "divisor" |)
                    ],
                    make_dict []
                  |)
                |)
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_signed" |),
        make_list [
          M.get_name (| globals, locals_stack, "quotient" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom sdiv_in_globals :
  IsInGlobals globals "sdiv" (make_function sdiv).

Definition mod_ : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Modulo remainder of the top two elements of the stack. Pushes the result
    back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "x" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "y" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "remainder" ,
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "remainder" ,
          BinOp.mod_ (|
            M.get_name (| globals, locals_stack, "x" |),
            M.get_name (| globals, locals_stack, "y" |)
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "remainder" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom mod__in_globals :
  IsInGlobals globals "mod" (make_function mod_).

Definition smod : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Signed modulo remainder of the top two elements of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "x" ,
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_signed" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y" ,
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "pop" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
          ],
          make_dict []
        |), "to_signed" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "y" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "remainder" ,
          Constant.int 0
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "remainder" ,
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, locals_stack, "get_sign" |),
              make_list [
                M.get_name (| globals, locals_stack, "x" |)
              ],
              make_dict []
            |),
            BinOp.mod_ (|
              M.call (|
                M.get_name (| globals, locals_stack, "abs" |),
                make_list [
                  M.get_name (| globals, locals_stack, "x" |)
                ],
                make_dict []
              |),
              M.call (|
                M.get_name (| globals, locals_stack, "abs" |),
                make_list [
                  M.get_name (| globals, locals_stack, "y" |)
                ],
                make_dict []
              |)
            |)
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_signed" |),
        make_list [
          M.get_name (| globals, locals_stack, "remainder" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom smod_in_globals :
  IsInGlobals globals "smod" (make_function smod).

Definition addmod : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Modulo addition of the top 2 elements with the 3rd element. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "x" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "z" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
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
      M.get_name (| globals, locals_stack, "GAS_MID" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "z" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "result" ,
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "result" ,
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              BinOp.mod_ (|
                BinOp.add (|
                  M.get_name (| globals, locals_stack, "x" |),
                  M.get_name (| globals, locals_stack, "y" |)
                |),
                M.get_name (| globals, locals_stack, "z" |)
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom addmod_in_globals :
  IsInGlobals globals "addmod" (make_function addmod).

Definition mulmod : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Modulo multiplication of the top 2 elements with the 3rd element. Pushes
    the result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "x" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "y" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "z" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
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
      M.get_name (| globals, locals_stack, "GAS_MID" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "z" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "result" ,
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              Constant.int 0
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "result" ,
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              BinOp.mod_ (|
                BinOp.mult (|
                  M.get_name (| globals, locals_stack, "x" |),
                  M.get_name (| globals, locals_stack, "y" |)
                |),
                M.get_name (| globals, locals_stack, "z" |)
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom mulmod_in_globals :
  IsInGlobals globals "mulmod" (make_function mulmod).

Definition exp : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Exponential operation of the top 2 elements. Pushes the result back on
    the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "base" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "exponent" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pop" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "exponent_bits" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "exponent" |), "bit_length" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "exponent_bytes" ,
      BinOp.floor_div (|
        BinOp.add (|
          M.get_name (| globals, locals_stack, "exponent_bits" |),
          Constant.int 7
        |),
        Constant.int 8
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      BinOp.add (|
        M.get_name (| globals, locals_stack, "GAS_EXPONENTIATION" |),
        BinOp.mult (|
          M.get_name (| globals, locals_stack, "GAS_EXPONENTIATION_PER_BYTE" |),
          M.get_name (| globals, locals_stack, "exponent_bytes" |)
        |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "result" ,
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "pow" |),
            make_list [
              M.get_name (| globals, locals_stack, "base" |);
              M.get_name (| globals, locals_stack, "exponent" |);
              M.get_name (| globals, locals_stack, "U256_CEIL_VALUE" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom exp_in_globals :
  IsInGlobals globals "exp" (make_function exp).

Definition signextend : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Sign extend operation. In other words, extend a signed number which
    fits in N bytes to 32 bytes.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "byte_num" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "value" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "charge_gas" |),
    make_list [
      M.get_name (| globals, locals_stack, "evm" |);
      M.get_name (| globals, locals_stack, "GAS_LOW" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.get_name (| globals, locals_stack, "byte_num" |),
          Constant.int 31
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "result" ,
          M.get_name (| globals, locals_stack, "value" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "value_bytes" ,
          M.call (|
            M.get_name (| globals, locals_stack, "bytes" |),
            make_list [
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "value" |), "to_be_bytes32" |),
                make_list [],
                make_dict []
              |)
            ],
            make_dict []
          |)
        |) in
        let _ := M.assign_local (|
          "value_bytes" ,
          M.slice (|
            M.get_name (| globals, locals_stack, "value_bytes" |),
            BinOp.sub (|
              Constant.int 31,
              M.call (|
                M.get_name (| globals, locals_stack, "int" |),
                make_list [
                  M.get_name (| globals, locals_stack, "byte_num" |)
                ],
                make_dict []
              |)
            |),
            Constant.None_,
            Constant.None_
          |)
        |) in
        let _ := M.assign_local (|
          "sign_bit" ,
          BinOp.r_shift (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "value_bytes" |),
              Constant.int 0
            |),
            Constant.int 7
          |)
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_name (| globals, locals_stack, "sign_bit" |),
              Constant.int 0
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "result" ,
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
                make_list [
                  M.get_name (| globals, locals_stack, "value_bytes" |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "num_bytes_prepend" ,
              BinOp.sub (|
                Constant.int 32,
                BinOp.add (|
                  M.get_name (| globals, locals_stack, "byte_num" |),
                  Constant.int 1
                |)
              |)
            |) in
            let _ := M.assign_local (|
              "result" ,
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "U256" |), "from_be_bytes" |),
                make_list [
                  BinOp.add (|
                    M.call (|
                      M.get_name (| globals, locals_stack, "bytearray" |),
                      make_list [
                        BinOp.mult (|
                          make_list [
                            Constant.int 255
                          ],
                          M.get_name (| globals, locals_stack, "num_bytes_prepend" |)
                        |)
                      ],
                      make_dict []
                    |),
                    M.get_name (| globals, locals_stack, "value_bytes" |)
                  |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "push" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |);
      M.get_name (| globals, locals_stack, "result" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_op (|
      BinOp.add,
      M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "pc" |),
      Constant.int 1
    |) in
    M.pure Constant.None_)).

Axiom signextend_in_globals :
  IsInGlobals globals "signextend" (make_function signextend).
