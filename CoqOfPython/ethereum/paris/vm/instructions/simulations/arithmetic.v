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

(* For sanity checks *)
Axiom environment : __init__.Environment.t.
Axiom message : __init__.Message.t Evm.t.

Definition empty_evm : Evm.t :=
  Evm.Make message {|
    Evm.Rest.pc := Uint.Make 0;
    Evm.Rest.stack := [];
    Evm.Rest.memory := [];
    Evm.Rest.code := __init__.Bytes.Make [];
    Evm.Rest.gas_left := Uint.Make 0;
    Evm.Rest.env := environment;
    Evm.Rest.valid_jump_destinations := [];
    Evm.Rest.logs := [];
    Evm.Rest.refund_counter := 0;
    Evm.Rest.running := true;
    Evm.Rest.output := __init__.Bytes.Make [];
    Evm.Rest.accounts_to_delete := [];
    Evm.Rest.touched_accounts := [];
    Evm.Rest.return_data := __init__.Bytes.Make [];
    Evm.Rest.error := None;
    Evm.Rest.accessed_addresses := [];
    Evm.Rest.accessed_storage_keys := [];
  |}.

Definition evm_with_gas : Evm.t :=
  Evm.Lens.gas_left.(Lens.write) empty_evm GAS_VERY_LOW.

Definition evm_with_stack : Evm.t :=
  Evm.Lens.stack.(Lens.write) evm_with_gas [
    U256.of_Z 23;
    U256.of_Z 3;
    U256.of_Z 5
  ].

Definition wrapped_binary_operation wrapped_operation gas_charge : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  letS? y := StateError.lift_lens Evm.Lens.stack pop in

  (* GAS *)
  letS? _ := charge_gas gas_charge in

  (* OPERATION *)
  let result := wrapped_operation x y in

  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in

  returnS? tt.

Definition add : MS? Evm.t Exception.t unit :=
  wrapped_binary_operation U256.wrapping_add GAS_VERY_LOW.

(* Compute add evm_with_stack. *)

Definition sub : MS? Evm.t Exception.t unit :=
  wrapped_binary_operation U256.wrapping_sub GAS_VERY_LOW.
  
(* Compute sub evm_with_stack. *)

Definition mul : MS? Evm.t Exception.t unit :=
  wrapped_binary_operation U256.wrapping_mul GAS_VERY_LOW.

(* Compute mul evm_with_stack. *)

Definition div : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? divisor := StateError.lift_lens Evm.Lens.stack pop in
  letS? divident := StateError.lift_lens Evm.Lens.stack pop in

  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in

  (* OPERATION *)

  let division := 
    match (U256.to_Z divident) with
    | 0 =>
      U256.of_Z 0
    | _ =>
      U256.of_Z ((U256.to_Z divisor) / (U256.to_Z divident))
  end in

  let result := division in
  
  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in

  returnS? tt.

(* Compute div evm_with_stack. *)

(* Name collides with Coq's mod. *)

Definition modulo : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  letS? y := StateError.lift_lens Evm.Lens.stack pop in

  (* GAS *)
  letS? _ := charge_gas GAS_VERY_LOW in

  (* OPERATION *)

  let modular y := 
    match (U256.to_Z y) with
    | 0 =>
      U256.of_Z 0
    | _ =>
        U256.of_Z ((U256.to_Z x) mod (U256.to_Z y))
  end
  in

  let result := modular y in
  
  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in

  returnS? tt.
  
(* Compute modulo evm_with_stack. *)

Definition add_mod : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  letS? y := StateError.lift_lens Evm.Lens.stack pop in
  letS? z := StateError.lift_lens Evm.Lens.stack pop in
        
  (* GAS *)
  letS? _ := charge_gas GAS_MID in

  (* OPERATION *)

  let addition_modular y := 
  match (U256.to_Z y) with
  | 0 =>
    U256.of_Z 0
  | _ =>
      U256.of_Z (((U256.to_Z x) + (U256.to_Z y)) mod (U256.to_Z z))
  end
  in

  let result := addition_modular y in
  
  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in

  returnS? tt.

(* Compute add_mod evm_with_stack. *)

Definition mul_mod : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? x := StateError.lift_lens Evm.Lens.stack pop in
  letS? y := StateError.lift_lens Evm.Lens.stack pop in
  letS? z := StateError.lift_lens Evm.Lens.stack pop in
        
  (* GAS *)
  letS? _ := charge_gas GAS_MID in

  (* OPERATION *)

  let multiplication_modular y := 
    match (U256.to_Z y) with
    | 0 =>
      U256.of_Z 0
    | _ =>
      U256.of_Z (((U256.to_Z x) * (U256.to_Z y)) mod (U256.to_Z z))
  end
  in

  let result := multiplication_modular y in
  
  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in

  returnS? tt.


(* Compute mul_mod evm_with_stack. *)

(* "This is equivalent to 1 + floor(log(y, 256))" *)

Definition byte_length n :=
  1 + Z.log2(n) / 8.

Definition exp : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? base := StateError.lift_lens Evm.Lens.stack pop in
  letS? exponent := StateError.lift_lens Evm.Lens.stack pop in

  let exponent_bytes := byte_length (U256.to_Z exponent) in
  (* GAS *)
  letS? _ := charge_gas (gas.Uint.Make 
                           ((gas.Uint.get GAS_EXPONENTIATION)
                          + (gas.Uint.get GAS_EXPONENTIATION_PER_BYTE)
                          * exponent_bytes)) in 

  (* OPERATION *)

  let result := U256.of_Z ((Z.pow (U256.to_Z base) (U256.to_Z exponent)) mod U256_CEIL_VALUE) in 
          
  
  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in

  returnS? tt.

(* Compute exp evm_with_stack. *)
