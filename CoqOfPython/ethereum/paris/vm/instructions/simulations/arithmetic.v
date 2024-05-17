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
    U256.of_Z 3
  ].

Definition binary_operation wrapped_operation gas_charge : MS? Evm.t Exception.t unit :=
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
  binary_operation U256.wrapping_add GAS_VERY_LOW.

(* Compute add evm_with_stack. *)

Definition sub : MS? Evm.t Exception.t unit :=
  binary_operation U256.wrapping_sub GAS_VERY_LOW.
  
(* Compute sub evm_with_stack. *)

Definition mul : MS? Evm.t Exception.t unit :=
  binary_operation U256.wrapping_mul GAS_VERY_LOW.

(* Compute mul evm_with_stack. *)

Definition div : MS? Evm.t Exception.t unit :=
  binary_operation U256.wrapping_div GAS_VERY_LOW.

(* Compute div evm_with_stack. *)

(* Gallina has a built in 'mod' which causes the
   names to collide *)

Definition sim_mod : MS? Evm.t Exception.t unit :=
  binary_operation U256.wrapping_mod GAS_VERY_LOW.

Require Import NZAxioms NZMulOrder NZPow.


Search "_" inside Z.

Check log2.


Definition exp : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? base := StateError.lift_lens Evm.Lens.stack pop in
  letS? exponent := StateError.lift_lens Evm.Lens.stack pop in

        
  (* GAS *)
  letS? _ := charge_gas GAS_EXPONENTIATION + GAS_EXPONENTIATION_PER_BYTE * exponent_bytes in

  (* OPERATION *)
  let result := U256.wrapping_div base exponent in

  letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in

  returnS? tt.





  
(* Compute sim_mod evm_with_stack. *)







    









