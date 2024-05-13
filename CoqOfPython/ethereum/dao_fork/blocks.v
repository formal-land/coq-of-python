Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.dao_fork.blocks".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
A `Block` is a single link in the chain that is Ethereum. Each `Block` contains
a `Header` and zero or more transactions. Each `Header` contains associated
metadata like the block number, parent block hash, and how much gas was
consumed by its transactions.

Together, these blocks form a cryptographically secure journal recording the
history of all state transitions that have happened since the genesis of the
chain.
".

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes8 :
  IsImported globals "ethereum.base_types" "Bytes8".
Axiom ethereum_base_types_imports_Bytes32 :
  IsImported globals "ethereum.base_types" "Bytes32".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".
Axiom ethereum_base_types_imports_slotted_freezable :
  IsImported globals "ethereum.base_types" "slotted_freezable".

Axiom ethereum_crypto_hash_imports_Hash32 :
  IsImported globals "ethereum.crypto.hash" "Hash32".

Axiom ethereum_dao_fork_fork_types_imports_Address :
  IsImported globals "ethereum.dao_fork.fork_types" "Address".
Axiom ethereum_dao_fork_fork_types_imports_Bloom :
  IsImported globals "ethereum.dao_fork.fork_types" "Bloom".
Axiom ethereum_dao_fork_fork_types_imports_Root :
  IsImported globals "ethereum.dao_fork.fork_types" "Root".

Axiom ethereum_dao_fork_transactions_imports_Transaction :
  IsImported globals "ethereum.dao_fork.transactions" "Transaction".

Definition Header : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition Block : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition Log : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition Receipt : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].
