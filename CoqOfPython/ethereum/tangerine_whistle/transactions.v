Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Transactions are atomic units of work created externally to Ethereum and
submitted to be executed. If Ethereum is viewed as a state machine,
transactions are the events that move between states.
".

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require typing.
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".
Axiom ethereum_base_types_Bytes0 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes0".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".
Axiom ethereum_base_types_slotted_freezable :
  IsGlobalAlias globals ethereum.base_types.globals "slotted_freezable".

Require ethereum.tangerine_whistle.fork_types.
Axiom ethereum_tangerine_whistle_fork_types_Address :
  IsGlobalAlias globals ethereum.tangerine_whistle.fork_types.globals "Address".

Definition TX_BASE_COST : Value.t := M.run ltac:(M.monadic (
  Constant.int 21000
)).

Definition TX_DATA_COST_PER_NON_ZERO : Value.t := M.run ltac:(M.monadic (
  Constant.int 68
)).

Definition TX_DATA_COST_PER_ZERO : Value.t := M.run ltac:(M.monadic (
  Constant.int 4
)).

Definition TX_CREATE_COST : Value.t := M.run ltac:(M.monadic (
  Constant.int 32000
)).

Definition Transaction : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].
