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

Require base_types.
Axiom base_types_U64 :
  IsGlobalAlias globals base_types.globals "U64".
Axiom base_types_U256 :
  IsGlobalAlias globals base_types.globals "U256".
Axiom base_types_Bytes :
  IsGlobalAlias globals base_types.globals "Bytes".
Axiom base_types_Bytes8 :
  IsGlobalAlias globals base_types.globals "Bytes8".
Axiom base_types_Bytes32 :
  IsGlobalAlias globals base_types.globals "Bytes32".
Axiom base_types_Uint :
  IsGlobalAlias globals base_types.globals "Uint".
Axiom base_types_slotted_freezable :
  IsGlobalAlias globals base_types.globals "slotted_freezable".

Require crypto.hash.
Axiom crypto_hash_Hash32 :
  IsGlobalAlias globals crypto.hash.globals "Hash32".

Require fork_types.
Axiom fork_types_Address :
  IsGlobalAlias globals fork_types.globals "Address".
Axiom fork_types_Bloom :
  IsGlobalAlias globals fork_types.globals "Bloom".
Axiom fork_types_Root :
  IsGlobalAlias globals fork_types.globals "Root".

Require transactions.
Axiom transactions_LegacyTransaction :
  IsGlobalAlias globals transactions.globals "LegacyTransaction".

Definition Withdrawal : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

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
