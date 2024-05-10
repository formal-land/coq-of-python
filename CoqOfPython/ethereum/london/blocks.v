Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require typing.
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Require ethereum.base_types.
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".
Axiom ethereum_base_types_Bytes8 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes8".
Axiom ethereum_base_types_Bytes32 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes32".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".
Axiom ethereum_base_types_slotted_freezable :
  IsGlobalAlias globals ethereum.base_types.globals "slotted_freezable".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_Hash32 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "Hash32".

Require ethereum.london.fork_types.
Axiom ethereum_london_fork_types_Address :
  IsGlobalAlias globals ethereum.london.fork_types.globals "Address".
Axiom ethereum_london_fork_types_Bloom :
  IsGlobalAlias globals ethereum.london.fork_types.globals "Bloom".
Axiom ethereum_london_fork_types_Root :
  IsGlobalAlias globals ethereum.london.fork_types.globals "Root".

Require ethereum.london.transactions.
Axiom ethereum_london_transactions_LegacyTransaction :
  IsGlobalAlias globals ethereum.london.transactions.globals "LegacyTransaction".

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
