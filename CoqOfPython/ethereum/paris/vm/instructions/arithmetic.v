Require Import CoqOfPython.CoqOfPython.

Definition expr_1 : Value.t :=
  (Value.String "
Ethereum Virtual Machine (EVM) Arithmetic Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementations of the EVM Arithmetic instructions.
").

Module import_ethereum_base_types.
  Require Import ethereum.base_types.
  Definition U255_CEIL_VALUE := U255_CEIL_VALUE.
  Definition U256 := U256.
  Definition U256_CEIL_VALUE := U256_CEIL_VALUE.
  Definition Uint := Uint.
End import_ethereum_base_types.
Import import_ethereum_base_types.

Module import_ethereum_utils_numeric.
  Require Import ethereum.utils.numeric.
  Definition get_sign := get_sign.
End import_ethereum_utils_numeric.
Import import_ethereum_utils_numeric.

Module import___init__.
  Require Import __init__.
  Definition Evm := Evm.
End import___init__.
Import import___init__.

Module import_gas.
  Require Import gas.
  Definition GAS_EXPONENTIATION := GAS_EXPONENTIATION.
  Definition GAS_EXPONENTIATION_PER_BYTE := GAS_EXPONENTIATION_PER_BYTE.
  Definition GAS_LOW := GAS_LOW.
  Definition GAS_MID := GAS_MID.
  Definition GAS_VERY_LOW := GAS_VERY_LOW.
  Definition charge_gas := charge_gas.
End import_gas.
Import import_gas.

Module import_stack.
  Require Import stack.
  Definition pop := pop.
  Definition push := push.
End import_stack.
Import import_stack.

Definition add (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Adds the top two elements of the stack together, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let x := (M.call (| pop, [evm.stack] |)) in
  let y := (M.call (| pop, [evm.stack] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_VERY_LOW] |)) in
  let result := (M.call (| x.wrapping_add, [y] |)) in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition sub (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Subtracts the top two elements of the stack, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let x := (M.call (| pop, [evm.stack] |)) in
  let y := (M.call (| pop, [evm.stack] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_VERY_LOW] |)) in
  let result := (M.call (| x.wrapping_sub, [y] |)) in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition mul (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Multiply the top two elements of the stack, and pushes the result back
    on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let x := (M.call (| pop, [evm.stack] |)) in
  let y := (M.call (| pop, [evm.stack] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_LOW] |)) in
  let result := (M.call (| x.wrapping_mul, [y] |)) in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition div (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Integer division of the top two elements of the stack. Pushes the result
    back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let dividend := (M.call (| pop, [evm.stack] |)) in
  let divisor := (M.call (| pop, [evm.stack] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_LOW] |)) in
  let _ :=
    if M.is_true (Compare.Eq (| divisor, (Value.Integer 0) |)) then
      let quotient := (M.call (| U256, [(Value.Integer 0)] |)) in
    else
      let quotient := (BinOp.FloorDiv dividend divisor) in in
  let _ := (M.call (| push, [evm.stack; quotient] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition sdiv (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Signed integer division of the top two elements of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let dividend := (M.call (| (M.call (| pop, [evm.stack] |)).to_signed, [] |)) in
  let divisor := (M.call (| (M.call (| pop, [evm.stack] |)).to_signed, [] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_LOW] |)) in
  let _ :=
    if M.is_true (Compare.Eq (| divisor, (Value.Integer 0) |)) then
      let quotient := (Value.Integer 0) in
    else
      let _ :=
        if M.is_true (BoolOp.And(Compare.Eq (| dividend, (UnOp.SubU255_CEIL_VALUE) |)) (Compare.Eq (| divisor, (UnOp.Sub(Value.Integer 1)) |))) then
          let quotient := (UnOp.SubU255_CEIL_VALUE) in
        else
          let sign := (M.call (| get_sign, [(BinOp.Mult dividend divisor)] |)) in
          let quotient := (BinOp.Mult sign (BinOp.FloorDiv (M.call (| abs, [dividend] |)) (M.call (| abs, [divisor] |)))) in in in
  let _ := (M.call (| push, [evm.stack; (M.call (| U256.from_signed, [quotient] |))] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition mod (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Modulo remainder of the top two elements of the stack. Pushes the result
    back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let x := (M.call (| pop, [evm.stack] |)) in
  let y := (M.call (| pop, [evm.stack] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_LOW] |)) in
  let _ :=
    if M.is_true (Compare.Eq (| y, (Value.Integer 0) |)) then
      let remainder := (M.call (| U256, [(Value.Integer 0)] |)) in
    else
      let remainder := (BinOp.Mod x y) in in
  let _ := (M.call (| push, [evm.stack; remainder] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition smod (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Signed modulo remainder of the top two elements of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let x := (M.call (| (M.call (| pop, [evm.stack] |)).to_signed, [] |)) in
  let y := (M.call (| (M.call (| pop, [evm.stack] |)).to_signed, [] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_LOW] |)) in
  let _ :=
    if M.is_true (Compare.Eq (| y, (Value.Integer 0) |)) then
      let remainder := (Value.Integer 0) in
    else
      let remainder := (BinOp.Mult (M.call (| get_sign, [x] |)) (BinOp.Mod (M.call (| abs, [x] |)) (M.call (| abs, [y] |)))) in in
  let _ := (M.call (| push, [evm.stack; (M.call (| U256.from_signed, [remainder] |))] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition addmod (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Modulo addition of the top 2 elements with the 3rd element. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let x := (M.call (| Uint, [(M.call (| pop, [evm.stack] |))] |)) in
  let y := (M.call (| Uint, [(M.call (| pop, [evm.stack] |))] |)) in
  let z := (M.call (| Uint, [(M.call (| pop, [evm.stack] |))] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_MID] |)) in
  let _ :=
    if M.is_true (Compare.Eq (| z, (Value.Integer 0) |)) then
      let result := (M.call (| U256, [(Value.Integer 0)] |)) in
    else
      let result := (M.call (| U256, [(BinOp.Mod (BinOp.Add x y) z)] |)) in in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition mulmod (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Modulo multiplication of the top 2 elements with the 3rd element. Pushes
    the result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let x := (M.call (| Uint, [(M.call (| pop, [evm.stack] |))] |)) in
  let y := (M.call (| Uint, [(M.call (| pop, [evm.stack] |))] |)) in
  let z := (M.call (| Uint, [(M.call (| pop, [evm.stack] |))] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_MID] |)) in
  let _ :=
    if M.is_true (Compare.Eq (| z, (Value.Integer 0) |)) then
      let result := (M.call (| U256, [(Value.Integer 0)] |)) in
    else
      let result := (M.call (| U256, [(BinOp.Mod (BinOp.Mult x y) z)] |)) in in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition exp (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Exponential operation of the top 2 elements. Pushes the result back on
    the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let base := (M.call (| Uint, [(M.call (| pop, [evm.stack] |))] |)) in
  let exponent := (M.call (| Uint, [(M.call (| pop, [evm.stack] |))] |)) in
  let exponent_bits := (M.call (| exponent.bit_length, [] |)) in
  let exponent_bytes := (BinOp.FloorDiv (BinOp.Add exponent_bits (Value.Integer 7)) (Value.Integer 8)) in
  let _ := (M.call (| charge_gas, [evm; (BinOp.Add GAS_EXPONENTIATION (BinOp.Mult GAS_EXPONENTIATION_PER_BYTE exponent_bytes))] |)) in
  let result := (M.call (| U256, [(M.call (| pow, [base; exponent; U256_CEIL_VALUE] |))] |)) in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.

Definition signextend (args : list Value.t) : M :=
  match args with
  | [evm] => ltac:(M.monadic (
  let _ := (Value.String "
    Sign extend operation. In other words, extend a signed number which
    fits in N bytes to 32 bytes.

    Parameters
    ----------
    evm :
        The current EVM frame.

    ") in
  let byte_num := (M.call (| pop, [evm.stack] |)) in
  let value := (M.call (| pop, [evm.stack] |)) in
  let _ := (M.call (| charge_gas, [evm; GAS_LOW] |)) in
  let _ :=
    if M.is_true (Compare.Gt (| byte_num, (Value.Integer 31) |)) then
      let result := value in
    else
      let value_bytes := (M.call (| bytes, [(M.call (| value.to_be_bytes32, [] |))] |)) in
      let value_bytes := value_bytes[(BinOp.Sub (Value.Integer 31) (M.call (| int, [byte_num] |))):(* At stmt: unsupported node type: NoneType *)] in
      let sign_bit := (BinOp.RShift value_bytes[(Value.Integer 0)] (Value.Integer 7)) in
      let _ :=
        if M.is_true (Compare.Eq (| sign_bit, (Value.Integer 0) |)) then
          let result := (M.call (| U256.from_be_bytes, [value_bytes] |)) in
        else
          let num_bytes_prepend := (BinOp.Sub (Value.Integer 32) (BinOp.Add byte_num (Value.Integer 1))) in
          let result := (M.call (| U256.from_be_bytes, [(BinOp.Add (M.call (| bytearray, [(BinOp.Mult [(Value.Integer 255)] num_bytes_prepend)] |)) value_bytes)] |)) in in in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.Add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.
