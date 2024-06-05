Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Module U256 := base_types.U256.
Module Uint := base_types.Uint.

Require ethereum.paris.vm.simulations.__init__.
Module Evm := __init__.Evm.


Require ethereum.paris.vm.simulations.gas.
Definition GAS_BASE := gas.GAS_BASE.
Definition GAS_HIGH := gas.GAS_HIGH.
Definition GAS_JUMPDEST := gas.GAS_JUMPDEST.
Definition GAS_MID := gas.GAS_MID.
Definition charge_gas := gas.charge_gas.

Require ethereum.paris.vm.simulations.exceptions.

(* TODO : Import in the InvalidJumpDestError exception *)

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
  Evm.Lens.gas_left.(Lens.write) empty_evm GAS_HIGH.

Definition evm_with_stack : Evm.t :=
  Evm.Lens.stack.(Lens.write) evm_with_gas [
    U256.of_Z 23;
    U256.of_Z 3;
    U256.of_Z 5
  ].

Definition stop : MS? Evm.t Exception.t unit :=
  (* STACK *)

  (* GAS *)

  (* OPERATION *)

  (* letS? _ := StateError.lift_lens Evm.Rest.running  in *)
      
  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
      
  returnS? tt.

(* How to check inside valid jump destinations? *)

Definition jump : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? jump_dest := StateError.lift_lens Evm.Lens.stack pop in
      
  (* GAS *)
  letS? _ := charge_gas GAS_MID in
  (* OPERATION *)

  (* letS? _ := StateError.lift_lens Evm.Rest.running  in *)
      
  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
      
  returnS? tt.

Definition jumpi : MS? Evm.t Exception.t unit :=
  (* STACK *)
  letS? jump_dest := StateError.lift_lens Evm.Lens.stack pop in
  letS? conditional_value := StateError.lift_lens Evm.Lens.stack pop in
      
  (* GAS *)
  letS? _ := charge_gas GAS_HIGH in
          
  (* OPERATION *)

  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
      
  returnS? tt.

Definition pc : MS? Evm.t Exception.t unit :=
  (* STACK *)
      
  (* GAS *)
  letS? _ := charge_gas GAS_BASE in
      
  (* OPERATION *)

  (* letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in *)

      
  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
      
  returnS? tt.

Definition gas_left : MS? Evm.t Exception.t unit :=
  (* STACK *)
      
  (* GAS *)
  letS? _ := charge_gas GAS_BASE in
      
  (* OPERATION *)

  (* letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in *)

      
  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
      
  returnS? tt.

Definition jumpdest : MS? Evm.t Exception.t unit :=
  (* STACK *)
      
  (* GAS *)
  letS? _ := charge_gas GAS_BASE in
      
  (* OPERATION *)

  (* letS? _ := StateError.lift_lens Evm.Lens.stack (push result) in *)

      
  (* PROGRAM COUNTER *)
  letS? _ := StateError.lift_lens Evm.Lens.pc (fun pc =>
    (inl tt, Uint.__add__ pc (Uint.Make 1))) in
      
  returnS? tt.
      


