Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.byzantium.blocks".

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

Axiom dataclasses_imports :
  AreImported globals "dataclasses" [ "dataclass" ].

Axiom typing_imports :
  AreImported globals "typing" [ "Tuple" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U256"; "Bytes"; "Bytes8"; "Bytes32"; "Uint"; "slotted_freezable" ].

Axiom ethereum_crypto_hash_imports :
  AreImported globals "ethereum.crypto.hash" [ "Hash32" ].

Axiom ethereum_byzantium_fork_types_imports :
  AreImported globals "ethereum.byzantium.fork_types" [ "Address"; "Bloom"; "Root" ].

Axiom ethereum_byzantium_transactions_imports :
  AreImported globals "ethereum.byzantium.transactions" [ "Transaction" ].

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
