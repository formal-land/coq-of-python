Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Definition U255_CEIL_VALUE := base_types.U255_CEIL_VALUE.
Module U256 := base_types.U256.
Definition U256_CEIL_VALUE := base_types.U256_CEIL_VALUE.
Module Uint := base_types.Uint.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.

Require ethereum.paris.vm.simulations.gas.
Definition GAS_EXPONENTIATION := gas.GAS_EXPONENTIATION.
Definition GAS_EXPONENTIATION_PER_BYTE := gas.GAS_EXPONENTIATION_PER_BYTE.
Definition GAS_LOW := gas.GAS_LOW.
Definition GAS_MID := gas.GAS_MID.
Definition GAS_VERY_LOW := gas.GAS_VERY_LOW.
Definition charge_gas := gas.charge_gas.

Require ethereum.paris.vm.simulations.stack.
Definition pop := stack.pop.
Definition push := stack.push.

Import simulations.CoqOfPython.Notations.
(* 
def bitwise_and(evm: Evm) -> None:
    """
    Bitwise AND operation of the top 2 elements of the stack. Pushes the
    result back on the stack.
    Parameters
    ----------
    evm :
        The current EVM frame.
    """
    # STACK
    x = pop(evm.stack)
    y = pop(evm.stack)
    # GAS
    charge_gas(evm, GAS_VERY_LOW)
    # OPERATION
    push(evm.stack, x & y)
    # PROGRAM COUNTER
    evm.pc += 1
*)
Definition bitwise_and : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  letS? y := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in
  (* OPERATION *)
  letS? _ := StateError.lift_lens Evm.Lens.stack (
    push (U256.bit_and x y)) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* 
def bitwise_or(evm: Evm) -> None:
    """
    Bitwise OR operation of the top 2 elements of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    """
    # STACK
    x = pop(evm.stack)
    y = pop(evm.stack)

    # GAS
    charge_gas(evm, GAS_VERY_LOW)

    # OPERATION
    push(evm.stack, x | y)

    # PROGRAM COUNTER
    evm.pc += 1
*)
Definition bitwise_or : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  letS? y := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in
  (* OPERATION *)
  letS? _ := StateError.lift_lens Evm.Lens.stack (
    push (U256.bit_or x y)) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* 
def bitwise_xor(evm: Evm) -> None:
    """
    Bitwise XOR operation of the top 2 elements of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    """
    # STACK
    x = pop(evm.stack)
    y = pop(evm.stack)

    # GAS
    charge_gas(evm, GAS_VERY_LOW)

    # OPERATION
    push(evm.stack, x ^ y)

    # PROGRAM COUNTER
    evm.pc += 1
*)
Definition bitwise_xor : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  letS? y := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in
  (* OPERATION *)
  letS? _ := StateError.lift_lens Evm.Lens.stack (
    push (U256.bit_xor x y)) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* 
def bitwise_not(evm: Evm) -> None:
    """
    Bitwise NOT operation of the top element of the stack. Pushes the
    result back on the stack.

    Parameters
    ----------
    evm :
        The current EVM frame.

    """
    # STACK
    x = pop(evm.stack)

    # GAS
    charge_gas(evm, GAS_VERY_LOW)

    # OPERATION
    push(evm.stack, ~x)

    # PROGRAM COUNTER
    evm.pc += 1
*)
Definition bitwise_not : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in
  (* OPERATION *)
  letS? _ := StateError.lift_lens Evm.Lens.stack (
    push (U256.bit_not x)) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* 
def get_byte(evm: Evm) -> None:
    """
    For a word (defined by next top element of the stack), retrieve the
    Nth byte (0-indexed and defined by top element of stack) from the
    left (most significant) to right (least significant).

    Parameters
    ----------
    evm :
        The current EVM frame.

    """
    # STACK
    byte_index = pop(evm.stack)
    word = pop(evm.stack)

    # GAS
    charge_gas(evm, GAS_VERY_LOW)

    # OPERATION
    if byte_index >= 32:
        result = U256(0)
    else:
        extra_bytes_to_right = 31 - byte_index
        # Remove the extra bytes in the right
        word = word >> (extra_bytes_to_right * 8)
        # Remove the extra bytes in the left
        word = word & 0xFF
        result = U256(word)

    push(evm.stack, result)

    # PROGRAM COUNTER
    evm.pc += 1
*)
Definition get_byte : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? byte_index := StateError.lift_lens Evm.Lens.stack pop in
  letS? word := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in
  (* OPERATION *)
  let result := 
    if ((U256.to_Z byte_index)>=? 32) 
    then (U256.of_Z 0) 
    else(
      let extra_bytes_to_right := 31 - (U256.to_Z byte_index)%Z in
      let word := (Z.shiftr (U256.to_Z word) (extra_bytes_to_right * 8)) in
      let word := Z.land word (0XFF%Z) in
      (U256.of_Z word)
    )
  in
  letS? _ := StateError.lift_lens Evm.Lens.stack (
    push result) in
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* def bitwise_shl(evm: Evm) -> None:
  """
  Logical shift left (SHL) operation of the top 2 elements of the stack.
  Pushes the result back on the stack.
  Parameters
  ----------
  evm :
      The current EVM frame.
  """
  # STACK
  shift = pop(evm.stack)
  value = pop(evm.stack)

  # GAS
  charge_gas(evm, GAS_VERY_LOW)

  # OPERATION
  if shift < 256:
      result = U256((value << shift) % U256_CEIL_VALUE)
  else:
      result = U256(0)

  push(evm.stack, result)

  # PROGRAM COUNTER
  evm.pc += 1 *)
Definition bitwise_shl : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? shift := StateError.lift_lens Evm.Lens.stack pop in
  letS? value := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in
  (* OPERATION *)
  let result :=
    if (U256.to_Z shift) <? 256 
    then (U256.of_Z (Z.shiftr (U256.to_Z value) (U256.to_Z shift))) 
    else (U256.of_Z 0) in
  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* def bitwise_shr(evm: Evm) -> None:
  """
  Logical shift right (SHR) operation of the top 2 elements of the stack.
  Pushes the result back on the stack.
  Parameters
  ----------
  evm :
      The current EVM frame.
  """
  # STACK
  shift = pop(evm.stack)
  value = pop(evm.stack)

  # GAS
  charge_gas(evm, GAS_VERY_LOW)

  # OPERATION
  if shift < 256:
      result = value >> shift
  else:
      result = U256(0)

  push(evm.stack, result)

  # PROGRAM COUNTER
  evm.pc += 1 *)
Definition bitwise_shr : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? shift := StateError.lift_lens Evm.Lens.stack pop in
  letS? value := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in
  (* OPERATION *)
  let result :=
    if (U256.to_Z shift) <? 256 
    then (U256.of_Z (Z.shiftr (U256.to_Z value) (U256.to_Z shift))) 
    else (U256.of_Z 0) in
  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.

(* 
def bitwise_sar(evm: Evm) -> None:
  """
  Arithmetic shift right (SAR) operation of the top 2 elements of the stack.
  Pushes the result back on the stack.
  Parameters
  ----------
  evm :
      The current EVM frame.
  """
  # STACK
  shift = pop(evm.stack)
  signed_value = pop(evm.stack).to_signed()

  # GAS
  charge_gas(evm, GAS_VERY_LOW)

  # OPERATION
  if shift < 256:
      result = U256.from_signed(signed_value >> shift)
  elif signed_value >= 0:
      result = U256(0)
  else:
      result = U256.MAX_VALUE

  push(evm.stack, result)

  # PROGRAM COUNTER
  evm.pc += 1 *)
Definition bitwise_sar : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? shift := StateError.lift_lens Evm.Lens.stack pop in
  letS? signed_value := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in
  (* OPERATION *)
  let result :=
    if (U256.to_Z shift) <? 256 
    then (U256.from_signed (U256.of_Z (Z.shiftr (U256.to_Z signed_value) (U256.to_Z shift))))
    else (
      if (U256.to_Z signed_value >=? 0)
      then (U256.of_Z 0) 
      else U256.MAX_VALUE) in
  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.
