Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Definition U255_CEIL_VALUE := base_types.U255_CEIL_VALUE.
Module U256 := base_types.U256.
Definition U256_CEIL_VALUE := base_types.U256_CEIL_VALUE.
Module Uint := base_types.Uint.
Definition to_be_bytes32 := base_types.Uint.to_be_bytes32.
Module Bytes := base_types.Bytes.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.
Module Message := __init__.Message.
Module State := __init__.State.
Module Address := __init__.Address.
Module Environment := __init__.Environment.

Require ethereum.paris.vm.simulations.gas.
Definition GAS_COLD_SLOAD := gas.GAS_COLD_SLOAD.
Definition GAS_WARM_ACCESS := gas.GAS_WARM_ACCESS.
Definition GAS_CALL_STIPEND := gas.GAS_CALL_STIPEND.
Definition GAS_STORAGE_UPDATE := gas.GAS_STORAGE_UPDATE.
Definition GAS_STORAGE_SET := gas.GAS_STORAGE_SET.
Definition GAS_STORAGE_CLEAR_REFUND := gas.GAS_STORAGE_CLEAR_REFUND.
Definition charge_gas := gas.charge_gas.

Require ethereum.paris.vm.simulations.stack.
Definition pop := stack.pop.
Definition push := stack.push.

Import simulations.CoqOfPython.Notations.

(* def get_storage(state: State, address: Address, key: Bytes) -> U256: *)
Definition get_storage (state : State.t) (address : Address.t) (key : Bytes.t) : U256.t. Admitted.
(* def get_storage_original(state: State, address: Address, key: Bytes) -> U256: *)
Definition get_storage_original (state : State.t) (address : Address.t) (key : Bytes.t) : U256.t. Admitted.

(* TODO: (progress) things to do on this draft:
- figure out a way to implement `list.contains` in coq
- finish sstore
*)

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
    letS? key := StateError.lift_lens Evm.Lens.stack pop in
    let key := Uint.Make (U256.to_Z key) in
    let key := to_be_bytes32 key in
    (* GAS *)
    letS? evm := readS? in
    let '(Evm.Make message rest) := evm in
    let evm_message_current_target := message.(Message.current_target) in
    let evm_rest_accessed_storage_keys := rest.(Evm.Rest.accessed_storage_keys) in
    letS? _ := 
    (* TODO: Fix the List.In *)
    if has_some (List.find 
    (* (evm_message_current_target, key)  *) _
    evm_rest_accessed_storage_keys)
    then charge_gas GAS_WARM_ACCESS
    else (
      (* TODO: check if the added element is added in the correct place *)
      (* NOTE: accessed_storage_keys.add is actually `pair.add` and we simulate it directly *)
      let evm_rest_accessed_storage_keys := 
        (evm_message_current_target, key) :: evm_rest_accessed_storage_keys in
      let rest := rest <| Evm.Rest.accessed_storage_keys := evm_rest_accessed_storage_keys |> in
      let evm := Evm.Make message rest in
      (* NOTE: After the state update, all previous variables like `evm_message_current_target`
               should not be put into use anymore. This seems unsatisfying. *)
      letS? _ := writeS? evm in
      charge_gas GAS_COLD_SLOAD)
    in
    (* OPERATION *)
    let evm_env_state := rest.(Evm.Rest.env).(Environment.state) in
    let value := get_storage evm_env_state evm_message_current_target key in
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
Definition sstore : MS? Evm.t Exception.t unit := 
  (* STACK *)
  (* 
  key = pop(evm.stack).to_be_bytes32()
  new_value = pop(evm.stack)
  if evm.gas_left <= GAS_CALL_STIPEND:
      raise OutOfGasError

  original_value = get_storage_original(
      evm.env.state, evm.message.current_target, key
  )
  current_value = get_storage(evm.env.state, evm.message.current_target, key)
  *)
  (* key = pop(evm.stack).to_be_bytes32() *)
  letS? key := StateError.lift_lens Evm.Lens.stack pop in
  let key := Uint.Make (U256.to_Z key) in
  let key := to_be_bytes32 key in

  letS? new_value := StateError.lift_lens Evm.Lens.stack pop in

  if _ 
  then 
  (* TODO: Fill in the correct error type *)
    StateError.lift_from_error (Error.raise (Exception.ArithmeticError ArithmeticError.OverflowError))
  else _ (* the full content of the rest of the code *)

  (* TODO: connect with the :? above *)
  letS? evm := readS? in
  let '(Evm.Make message message) := evm in
  let evm_env_state := rest.(Evm.Rest.env).(Environment.state) in
  let evm_message_current_target := message.(Message.current_target) in

  let original_value := get_storage_original evm_env_state evm_message_current_target key in
  let current_value := get_storage evm_env_state evm_message_current_target key in

  let gas_cost := Uint.Make 0 in

  (* if (evm.message.current_target, key) not in evm.accessed_storage_keys:
    evm.accessed_storage_keys.add((evm.message.current_target, key))
    gas_cost += GAS_COLD_SLOAD

  if original_value == current_value and current_value != new_value:
    if original_value == 0:
        gas_cost += GAS_STORAGE_SET
    else:
        gas_cost += GAS_STORAGE_UPDATE - GAS_COLD_SLOAD
  else:
    gas_cost += GAS_WARM_ACCESS *)
  letS? _ := 
  if ~(List.In (evm_message_current_target, key) evm_rest_accessed_storage_keys)
  then (
    (* evm.accessed_storage_keys.add((evm.message.current_target, key)) *)
    letS? _ := (* gas_cost += GAS_COLD_SLOAD *)
  )
  else tt in

  (* 
    if original_value == current_value and current_value != new_value:
        if original_value == 0:
            gas_cost += GAS_STORAGE_SET
        else:
            gas_cost += GAS_STORAGE_UPDATE - GAS_COLD_SLOAD
    else:
        gas_cost += GAS_WARM_ACCESS
  *)
  letS? _ :=
  if _ 
  then _ 
  else 

  (* 
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
  *)

  (* 
      charge_gas(evm, gas_cost)

  *)
  (* PROGRAM *)
  (*
    if evm.message.is_static:
        raise WriteInStaticContext
    set_storage(evm.env.state, evm.message.current_target, key, new_value)
  *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
  (inl tt, Uint.__add__ pc (Uint.Make 1))) in
  returnS? tt.
