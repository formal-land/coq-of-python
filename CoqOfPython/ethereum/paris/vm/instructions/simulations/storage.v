(* 
from ...state import get_storage, get_storage_original, set_storage
from .. import Evm
from ..exceptions import OutOfGasError, WriteInStaticContext
from ..gas import (
    GAS_CALL_STIPEND,
    GAS_COLD_SLOAD,
    GAS_STORAGE_CLEAR_REFUND,
    GAS_STORAGE_SET,
    GAS_STORAGE_UPDATE,
    GAS_WARM_ACCESS,
    charge_gas,
) *)

Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Definition U255_CEIL_VALUE := base_types.U255_CEIL_VALUE.
Module U256 := base_types.U256.
Definition U256_CEIL_VALUE := base_types.U256_CEIL_VALUE.
Module Uint := base_types.Uint.
Definition to_be_bytes32 := base_types.Uint.to_be_bytes32.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.
Module Message := __init__.Message.

Require ethereum.paris.vm.simulations.gas.
Definition GAS_COLD_SLOAD := gas.GAS_COLD_SLOAD.
Definition GAS_WARM_ACCESS := gas.GAS_WARM_ACCESS.
Definition GAS_VERY_LOW := gas.GAS_VERY_LOW.
Definition charge_gas := gas.charge_gas.

Require ethereum.paris.vm.simulations.stack.
Definition pop := stack.pop.
Definition push := stack.push.

Import simulations.CoqOfPython.Notations.

(* def sload(evm: Evm) -> None:
    """
    Loads to the stack, the value corresponding to a certain key from the
    storage of the current account.

    Parameters
    ----------
    evm :
        The current EVM frame.

    """
    # STACK
    key = pop(evm.stack).to_be_bytes32()

    # GAS
    if (evm.message.current_target, key) in evm.accessed_storage_keys:
        charge_gas(evm, GAS_WARM_ACCESS)
    else:
        evm.accessed_storage_keys.add((evm.message.current_target, key))
        charge_gas(evm, GAS_COLD_SLOAD)

    # OPERATION
    value = get_storage(evm.env.state, evm.message.current_target, key)

    push(evm.stack, value)

    # PROGRAM COUNTER
    evm.pc += 1 *)

Definition sload : MS? Evm.t Exception.t unit := 
    (* STACK *)
    (* key = pop(evm.stack).to_be_bytes32() *)
    letS? key := StateError.lift_lens Evm.Lens.stack pop in
    let key := Uint.Make (U256.to_Z key) in
    let key := to_be_bytes32 key in
    (* GAS *)
    (* 
    if (evm.message.current_target, key) in evm.accessed_storage_keys:
        charge_gas(evm, GAS_WARM_ACCESS)
    else:
        evm.accessed_storage_keys.add((evm.message.current_target, key))
        charge_gas(evm, GAS_COLD_SLOAD)
    *)
    letS? evm := readS? in
    let '(Evm.Make message rest) := evm in
    let evm_message_current_target := message.(Message.current_target) in
    let evm_rest_accessed_storage_keys := rest.(Evm.Rest.accessed_storage_keys) in
    (* NOTE: accessed_storage_keys.add is actually `pair.add` and now we just simulate directly *)
    (* TODO: list `is_in` function *)

    letS? _ := 
    if List.has evm_rest_accessed_storage_keys (evm_message_current_target, key)
    then charge_gas GAS_WARM_ACCESS
    else (let _ := (* evm.accessed_storage_keys.add((evm.message.current_target, key)) *)
      charge_gas GAS_COLD_SLOAD)
    in
    (* OPERATION *)
    (* 
    value = get_storage(evm.env.state, evm.message.current_target, key)
    push(evm.stack, value)
    *)
    (* TODO: implement get_storage *)
    let evm_env_state := rest.(Evm.Rest.env).(Environment.state) in
    let value := get_storage evm_env_state evm_message_current_target in
    letS? _ := StateError.lift_lens Evm.Lens.stack (push value) in 
    (* PROGRAM COUNTER *) 
    letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
    returnS? tt.


(* def sstore(evm: Evm) -> None:
    """
    Stores a value at a certain key in the current context's storage.

    Parameters
    ----------
    evm :
        The current EVM frame.

    """
    # STACK
    key = pop(evm.stack).to_be_bytes32()
    new_value = pop(evm.stack)
    if evm.gas_left <= GAS_CALL_STIPEND:
        raise OutOfGasError

    original_value = get_storage_original(
        evm.env.state, evm.message.current_target, key
    )
    current_value = get_storage(evm.env.state, evm.message.current_target, key)

    gas_cost = Uint(0)

    if (evm.message.current_target, key) not in evm.accessed_storage_keys:
        evm.accessed_storage_keys.add((evm.message.current_target, key))
        gas_cost += GAS_COLD_SLOAD

    if original_value == current_value and current_value != new_value:
        if original_value == 0:
            gas_cost += GAS_STORAGE_SET
        else:
            gas_cost += GAS_STORAGE_UPDATE - GAS_COLD_SLOAD
    else:
        gas_cost += GAS_WARM_ACCESS

    # Refund Counter Calculation
    if current_value != new_value:
        if original_value != 0 and current_value != 0 and new_value == 0:
            # Storage is cleared for the first time in the transaction
            evm.refund_counter += int(GAS_STORAGE_CLEAR_REFUND)

        if original_value != 0 and current_value == 0:
            # Gas refund issued earlier to be reversed
            evm.refund_counter -= int(GAS_STORAGE_CLEAR_REFUND)

        if original_value == new_value:
            # Storage slot being restored to its original value
            if original_value == 0:
                # Slot was originally empty and was SET earlier
                evm.refund_counter += int(GAS_STORAGE_SET - GAS_WARM_ACCESS)
            else:
                # Slot was originally non-empty and was UPDATED earlier
                evm.refund_counter += int(
                    GAS_STORAGE_UPDATE - GAS_COLD_SLOAD - GAS_WARM_ACCESS
                )

    charge_gas(evm, gas_cost)
    if evm.message.is_static:
        raise WriteInStaticContext
    set_storage(evm.env.state, evm.message.current_target, key, new_value)

    # PROGRAM COUNTER
    evm.pc += 1 *)
