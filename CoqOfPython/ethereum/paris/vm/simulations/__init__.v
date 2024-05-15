Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.

Require ethereum.simulations.base_types.
Module U64 := base_types.U64.
Module U256 := base_types.U256.
Module Bytes := base_types.Bytes.
Module Bytes0 := base_types.Bytes0.
Module Bytes32 := base_types.Bytes32.
Module Uint := base_types.Uint.

Require ethereum.crypto.simulations.hash.
Module Hash32 := hash.Hash32.

Require ethereum.paris.simulations.fork_types.
Module Address := fork_types.Address.

Require ethereum.paris.simulations.state.
Module State := state.State.

Module Environment.
  Record t : Set := {
    caller : Address.t;
    block_hashes : list Hash32.t;
    origin : Address.t;
    coinbase : Address.t;
    number : Uint.t;
    base_fee_per_gas : Uint.t;
    gas_limit : Uint.t;
    gas_price : Uint.t;
    time : U256.t;
    prev_randao : Bytes32.t;
    state : State.t;
    chain_id : U64.t;
    traces : list unit
  }.
End Environment.

Module Message.
  (** We parametrize this type by the environment. *)
  Record t {Evm : Set} : Set := {
    caller : Address.t;
    target : Bytes0.t + Address.t;
    current_target : Address.t;
    gas : Uint.t;
    value : U256.t;
    data : Bytes.t;
    code_address : option Address.t;
    code : Bytes.t;
    depth : Uint.t;
    should_transfer_value : bool;
    is_static : bool;
    accessed_addresses : list Address.t;
    accessed_storage_keys : list (Address.t * Bytes32.t);
    parent_evm : option Evm
  }.
  Arguments t : clear implicits.
End Message.

Module Evm.
  (** We split the record as it is recursive in the [message] field, and we cannot have recursive
      records. *)
  Module Rest.
    Record t : Set := {
      pc : Uint.t;
      stack : list (U256.t);
      (* memory : list ascii;
      code : Bytes.t; *)
      gas_left : Uint.t;
      (* env : Environment.t;
      valid_jump_destinations : list Uint.t;
      logs : list unit;
      refund_counter : Z;
      running : bool;
      output : Bytes.t;
      accounts_to_delete : list Address.t;
      touched_accounts : list Address.t;
      return_data : Bytes.t;
      error : option Exception.t;
      accessed_addresses : list Address.t;
      accessed_storage_keys : list (Address.t * Bytes32.t) *)
    }.
  End Rest.

  Inductive t : Set :=
  | Make (message : Message.t t) (rest : Rest.t).

  Module Lens.
    Definition message : Lens.t t (Message.t t) := {|
      Lens.read '(Make message _) := message;
      Lens.write '(Make _ rest) message := Make message rest;
    |}.

    Definition pc : Lens.t t Uint.t := {|
      Lens.read '(Make _ rest) := rest.(Rest.pc);
      Lens.write '(Make message rest) pc := Make message rest<|Rest.pc := pc|>;
    |}.

    Definition stack : Lens.t t (list U256.t) := {|
      Lens.read '(Make _ rest) := rest.(Rest.stack);
      Lens.write '(Make message rest) stack := Make message rest<|Rest.stack := stack|>;
    |}.

    (* Definition memory : Lens.t t (list ascii) := {|
      Lens.read '(Make _ rest) := rest.(Rest.memory);
      Lens.write '(Make message rest) memory := Make message rest<|Rest.memory := memory|>;
    |}.

    Definition code : Lens.t t Bytes.t := {|
      Lens.read '(Make _ rest) := rest.(Rest.code);
      Lens.write '(Make message rest) code := Make message rest<|Rest.code := code|>;
    |}. *)

    Definition gas_left : Lens.t t Uint.t := {|
      Lens.read '(Make _ rest) := rest.(Rest.gas_left);
      Lens.write '(Make message rest) gas_left := Make message rest<|Rest.gas_left := gas_left|>;
    |}.
  End Lens.
End Evm.
