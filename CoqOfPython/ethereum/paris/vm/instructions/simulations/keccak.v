Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Definition U255_CEIL_VALUE := base_types.U255_CEIL_VALUE.
Module U256 := base_types.U256.
Definition U256_CEIL_VALUE := base_types.U256_CEIL_VALUE.
Module Uint := base_types.Uint.

Definition bytearray := base_types.bytearray.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.

Require ethereum.paris.vm.simulations.gas.
Definition GAS_KECCAK256 := gas.GAS_KECCAK256.
Definition GAS_KECCAK256_WORD := gas.GAS_KECCAK256_WORD.
Definition calculate_gas_extend_memory := gas.calculate_gas_extend_memory.
Definition charge_gas := gas.charge_gas.

Require ethereum.paris.vm.simulations.stack.
Definition pop := stack.pop.
Definition push := stack.push.

Require ethereum.utils.simulations.numeric.
Definition ceil32 := numeric.ceil32.

Import simulations.CoqOfPython.Notations.

(* TODO: Check the axiomatized parts are done correctly *)
Axiom keccak256 (bytes : FixedBytes.t) : FixBytes.t.
(* 
  def memory_read_bytes(
      memory: bytearray, start_position: U256, size: U256
  ) -> bytearray:
*)
(* NOTE: Upon further implementations on `memory`, we can move this axiomatized function to `memory.py`. *)
Axiom memory_read_bytes (memory : bytearray) (start_position size : U256) : bytearray.

(* 
from ethereum.utils.numeric import ceil32

from .. import Evm
from ..gas import (
    GAS_KECCAK256,
    GAS_KECCAK256_WORD,
    calculate_gas_extend_memory,
    charge_gas,
)
from ..memory import memory_read_bytes
from ..stack import pop, push


def keccak(evm: Evm) -> None:
    """
    Pushes to the stack the Keccak-256 hash of a region of memory.

    This also expands the memory, in case the memory is insufficient to
    access the data's memory location.

    Parameters
    ----------
    evm :
        The current EVM frame.

    """
    # STACK
    memory_start_index = pop(evm.stack)
    size = pop(evm.stack)

    # GAS
    words = ceil32(Uint(size)) // 32
    word_gas_cost = GAS_KECCAK256_WORD * words
    extend_memory = calculate_gas_extend_memory(
        evm.memory, [(memory_start_index, size)]
    )
    charge_gas(evm, GAS_KECCAK256 + word_gas_cost + extend_memory.cost)

    # OPERATION
    evm.memory += b"\x00" * extend_memory.expand_by
    data = memory_read_bytes(evm.memory, memory_start_index, size)
    hash = keccak256(data)

    push(evm.stack, U256.from_be_bytes(hash))

    # PROGRAM COUNTER
    evm.pc += 1
*)
Definition bitwise_and : MS? Evm.t Exception.t unit := 
  (* STACK *)
  letS? memory_start_index := StateError.lift_lens Evm.Lens.stack pop in
  letS? size := StateError.lift_lens Evm.Lens.stack pop in
  (* GAS *)
  (* 
    words = ceil32(Uint(size)) // 32
    word_gas_cost = GAS_KECCAK256_WORD * words
    extend_memory = calculate_gas_extend_memory(
        evm.memory, [(memory_start_index, size)]
    )
    charge_gas(evm, GAS_KECCAK256 + word_gas_cost + extend_memory.cost)
  *)
  (* size : U256 -> Uint *)
  let words := ceil32(U256.to_Uint size) in
  let word_gas_cost := Uint.Make (Uint.get GAS_KECCAK256_WORD * Uint.get words) in

  (* Get evm.memory *)
  letS? evm := readS? in
  let '(Evm.Make _ rest) := evm in
  let evm_memory := rest.(Evm.Rest.memory) in

  let extend_memory := calculate_gas_extend_memory evm_memory (list (memory_start_index, size)) in (* TODO: Fix this *)

  letS? _ := charge_gas GAS_KECCAK256 + word_gas_cost + extend_memory.cost in
  (* OPERATION *)
  (* 
    evm.memory += b"\x00" * extend_memory.expand_by
    data = memory_read_bytes(evm.memory, memory_start_index, size)
    hash = keccak256(data)

    push(evm.stack, U256.from_be_bytes(hash))
  *)
  (* Construct correrctly the b"\x00" *)
  let b_x00 := base_types.FixedBytes.Make [Ascii.ascii_of_N 0] in
  let b_x00 := hash.Bytes32.Make b_x00 in
  let b_x00 := __init__.Hash32.Make b_x00 in

  let data := memory_read_bytes evm_memory memory_start_index size in
  let hash := keccak256 data in

  letS? _ := StateError.lift_lens Evm.Lens.stack (
    push (U256.make (FixedBytes.get hash))) in 
  (* PROGRAM COUNTER *) 
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.