Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.byzantium.transactions".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Transactions are atomic units of work created externally to Ethereum and
submitted to be executed. If Ethereum is viewed as a state machine,
transactions are the events that move between states.
".

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".
Axiom ethereum_base_types_imports_slotted_freezable :
  IsImported globals "ethereum.base_types" "slotted_freezable".

Axiom ethereum_byzantium_fork_types_imports_Address :
  IsImported globals "ethereum.byzantium.fork_types" "Address".

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

Definition Transaction : Value.t := builtins.make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.
