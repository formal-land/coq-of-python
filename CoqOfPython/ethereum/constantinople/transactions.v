Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.constantinople.transactions".

Definition expr_1 : Value.t :=
  Constant.str "
Transactions are atomic units of work created externally to Ethereum and
submitted to be executed. If Ethereum is viewed as a state machine,
transactions are the events that move between states.
".

Axiom dataclasses_imports :
  AreImported globals "dataclasses" [ "dataclass" ].

Axiom typing_imports :
  AreImported globals "typing" [ "Union" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U256"; "Bytes"; "Bytes0"; "Uint"; "slotted_freezable" ].

Axiom ethereum_constantinople_fork_types_imports :
  AreImported globals "ethereum.constantinople.fork_types" [ "Address" ].

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
