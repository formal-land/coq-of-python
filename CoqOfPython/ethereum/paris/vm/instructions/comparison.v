Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.paris.vm.instructions.comparison".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Comparison Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM Comparison instructions.
".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".

Axiom ethereum_paris_vm_imports_Evm :
  IsImported globals "ethereum.paris.vm" "Evm".

Axiom ethereum_paris_vm_gas_imports_GAS_VERY_LOW :
  IsImported globals "ethereum.paris.vm.gas" "GAS_VERY_LOW".
Axiom ethereum_paris_vm_gas_imports_charge_gas :
  IsImported globals "ethereum.paris.vm.gas" "charge_gas".

Axiom ethereum_paris_vm_stack_imports_pop :
  IsImported globals "ethereum.paris.vm.stack" "pop".
Axiom ethereum_paris_vm_stack_imports_push :
  IsImported globals "ethereum.paris.vm.stack" "push".

Definition less_than : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Checks if the top element is less than the next top element. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "left" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "right" ,
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
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Compare.lt (|
            M.get_name (| globals, locals_stack, "left" |),
            M.get_name (| globals, locals_stack, "right" |)
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

Axiom less_than_in_globals :
  IsInGlobals globals "less_than" (make_function less_than).

Definition signed_less_than : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Signed less-than comparison.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "left" ,
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
      "right" ,
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
      M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "result" ,
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Compare.lt (|
            M.get_name (| globals, locals_stack, "left" |),
            M.get_name (| globals, locals_stack, "right" |)
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

Axiom signed_less_than_in_globals :
  IsInGlobals globals "signed_less_than" (make_function signed_less_than).

Definition greater_than : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Checks if the top element is greater than the next top element. Pushes
    the result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "left" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "right" ,
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
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Compare.gt (|
            M.get_name (| globals, locals_stack, "left" |),
            M.get_name (| globals, locals_stack, "right" |)
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

Axiom greater_than_in_globals :
  IsInGlobals globals "greater_than" (make_function greater_than).

Definition signed_greater_than : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Signed greater-than comparison.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "left" ,
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
      "right" ,
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
      M.get_name (| globals, locals_stack, "GAS_VERY_LOW" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "result" ,
      M.call (|
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Compare.gt (|
            M.get_name (| globals, locals_stack, "left" |),
            M.get_name (| globals, locals_stack, "right" |)
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

Axiom signed_greater_than_in_globals :
  IsInGlobals globals "signed_greater_than" (make_function signed_greater_than).

Definition equal : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Checks if the top element is equal to the next top element. Pushes
    the result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    " in
    let _ := M.assign_local (|
      "left" ,
      M.call (|
        M.get_name (| globals, locals_stack, "pop" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "evm" |), "stack" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "right" ,
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
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Compare.eq (|
            M.get_name (| globals, locals_stack, "left" |),
            M.get_name (| globals, locals_stack, "right" |)
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

Axiom equal_in_globals :
  IsInGlobals globals "equal" (make_function equal).

Definition is_zero : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "evm" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Checks if the top element is equal to 0. Pushes the result back on the
    stack.

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
        M.get_name (| globals, locals_stack, "U256" |),
        make_list [
          Compare.eq (|
            M.get_name (| globals, locals_stack, "x" |),
            Constant.int 0
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

Axiom is_zero_in_globals :
  IsInGlobals globals "is_zero" (make_function is_zero).
