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

Require ethereum.base_types.
Definition U255_CEIL_VALUE := U255_CEIL_VALUE.
Definition U256 := U256.
Definition U256_CEIL_VALUE := U256_CEIL_VALUE.
Definition Uint := Uint.

Require ethereum.utils.numeric.
Definition get_sign := get_sign.

Require __init__.
Definition Evm := Evm.

Require gas.
Definition GAS_EXPONENTIATION := GAS_EXPONENTIATION.
Definition GAS_EXPONENTIATION_PER_BYTE := GAS_EXPONENTIATION_PER_BYTE.
Definition GAS_LOW := GAS_LOW.
Definition GAS_MID := GAS_MID.
Definition GAS_VERY_LOW := GAS_VERY_LOW.
Definition charge_gas := charge_gas.

Require stack.
Definition pop := pop.
Definition push := push.

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
    BinOp.add,
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
    BinOp.add,
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
    BinOp.add,
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
    if M.is_true (Compare.eq (| divisor, (Value.Integer 0) |)) then
      let quotient := (M.call (| U256, [(Value.Integer 0)] |)) in
    else
      let quotient := BinOp.floor_div (| dividend, divisor |) in in
  let _ := (M.call (| push, [evm.stack; quotient] |)) in
  let _ := M.assign_op (|
    BinOp.add,
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
    if M.is_true (Compare.eq (| divisor, (Value.Integer 0) |)) then
      let quotient := (Value.Integer 0) in
    else
      let _ :=
        if M.is_true (BoolOp.and(Compare.eq (| dividend, (UnOp.subU255_CEIL_VALUE) |)) (Compare.eq (| divisor, (UnOp.sub(Value.Integer 1)) |))) then
          let quotient := (UnOp.subU255_CEIL_VALUE) in
        else
          let sign := (M.call (| get_sign, [BinOp.mult (| dividend, divisor |)] |)) in
          let quotient := BinOp.mult (| sign, BinOp.floor_div (| (M.call (| abs, [dividend] |)), (M.call (| abs, [divisor] |)) |) |) in in in
  let _ := (M.call (| push, [evm.stack; (M.call (| U256.from_signed, [quotient] |))] |)) in
  let _ := M.assign_op (|
    BinOp.add,
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
    if M.is_true (Compare.eq (| y, (Value.Integer 0) |)) then
      let remainder := (M.call (| U256, [(Value.Integer 0)] |)) in
    else
      let remainder := BinOp.mod_ (| x, y |) in in
  let _ := (M.call (| push, [evm.stack; remainder] |)) in
  let _ := M.assign_op (|
    BinOp.add,
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
    if M.is_true (Compare.eq (| y, (Value.Integer 0) |)) then
      let remainder := (Value.Integer 0) in
    else
      let remainder := BinOp.mult (| (M.call (| get_sign, [x] |)), BinOp.mod_ (| (M.call (| abs, [x] |)), (M.call (| abs, [y] |)) |) |) in in
  let _ := (M.call (| push, [evm.stack; (M.call (| U256.from_signed, [remainder] |))] |)) in
  let _ := M.assign_op (|
    BinOp.add,
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
    if M.is_true (Compare.eq (| z, (Value.Integer 0) |)) then
      let result := (M.call (| U256, [(Value.Integer 0)] |)) in
    else
      let result := (M.call (| U256, [BinOp.mod_ (| BinOp.add (| x, y |), z |)] |)) in in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.add,
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
    if M.is_true (Compare.eq (| z, (Value.Integer 0) |)) then
      let result := (M.call (| U256, [(Value.Integer 0)] |)) in
    else
      let result := (M.call (| U256, [BinOp.mod_ (| BinOp.mult (| x, y |), z |)] |)) in in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.add,
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
  let exponent_bytes := BinOp.floor_div (| BinOp.add (| exponent_bits, (Value.Integer 7) |), (Value.Integer 8) |) in
  let _ := (M.call (| charge_gas, [evm; BinOp.add (| GAS_EXPONENTIATION, BinOp.mult (| GAS_EXPONENTIATION_PER_BYTE, exponent_bytes |) |)] |)) in
  let result := (M.call (| U256, [(M.call (| pow, [base; exponent; U256_CEIL_VALUE] |))] |)) in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.add,
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
    if M.is_true (Compare.gt (| byte_num, (Value.Integer 31) |)) then
      let result := value in
    else
      let value_bytes := (M.call (| bytes, [(M.call (| value.to_be_bytes32, [] |))] |)) in
      let value_bytes := value_bytes[BinOp.sub (| (Value.Integer 31), (M.call (| int, [byte_num] |)) |):(* At stmt: unsupported node type: NoneType *)] in
      let sign_bit := BinOp.r_shift (| value_bytes[(Value.Integer 0)], (Value.Integer 7) |) in
      let _ :=
        if M.is_true (Compare.eq (| sign_bit, (Value.Integer 0) |)) then
          let result := (M.call (| U256.from_be_bytes, [value_bytes] |)) in
        else
          let num_bytes_prepend := BinOp.sub (| (Value.Integer 32), BinOp.add (| byte_num, (Value.Integer 1) |) |) in
          let result := (M.call (| U256.from_be_bytes, [BinOp.add (| (M.call (| bytearray, [BinOp.mult (| [(Value.Integer 255)], num_bytes_prepend |)] |)), value_bytes |)] |)) in in in
  let _ := (M.call (| push, [evm.stack; result] |)) in
  let _ := M.assign_op (|
    BinOp.add,
    evm.pc,
    (Value.Integer 1)
  |) in))
  | _ => M.impossible
  end.
