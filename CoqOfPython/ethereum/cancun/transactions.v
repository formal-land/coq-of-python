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
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Require __init__.
Axiom __init___rlp :
  IsGlobalAlias globals __init__.globals "rlp".

Require base_types.
Axiom base_types_U64 :
  IsGlobalAlias globals base_types.globals "U64".
Axiom base_types_U256 :
  IsGlobalAlias globals base_types.globals "U256".
Axiom base_types_Bytes :
  IsGlobalAlias globals base_types.globals "Bytes".
Axiom base_types_Bytes0 :
  IsGlobalAlias globals base_types.globals "Bytes0".
Axiom base_types_Bytes32 :
  IsGlobalAlias globals base_types.globals "Bytes32".
Axiom base_types_Uint :
  IsGlobalAlias globals base_types.globals "Uint".
Axiom base_types_slotted_freezable :
  IsGlobalAlias globals base_types.globals "slotted_freezable".

Require exceptions.
Axiom exceptions_InvalidBlock :
  IsGlobalAlias globals exceptions.globals "InvalidBlock".

Require fork_types.
Axiom fork_types_Address :
  IsGlobalAlias globals fork_types.globals "Address".
Axiom fork_types_VersionedHash :
  IsGlobalAlias globals fork_types.globals "VersionedHash".

Definition TX_BASE_COST : Value.t := M.run ltac:(M.monadic (
  Constant.int 21000
)).

Definition TX_DATA_COST_PER_NON_ZERO : Value.t := M.run ltac:(M.monadic (
  Constant.int 16
)).

Definition TX_DATA_COST_PER_ZERO : Value.t := M.run ltac:(M.monadic (
  Constant.int 4
)).

Definition TX_CREATE_COST : Value.t := M.run ltac:(M.monadic (
  Constant.int 32000
)).

Definition TX_ACCESS_LIST_ADDRESS_COST : Value.t := M.run ltac:(M.monadic (
  Constant.int 2400
)).

Definition TX_ACCESS_LIST_STORAGE_KEY_COST : Value.t := M.run ltac:(M.monadic (
  Constant.int 1900
)).

Definition LegacyTransaction : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition AccessListTransaction : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition FeeMarketTransaction : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition BlobTransaction : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition Transaction : Value.t := M.run ltac:(M.monadic (
  M.get_subscript (| M.get_name (| globals, "Union" |), make_tuple [ M.get_name (| globals, "LegacyTransaction" |); M.get_name (| globals, "AccessListTransaction" |); M.get_name (| globals, "FeeMarketTransaction" |); M.get_name (| globals, "BlobTransaction" |) ] |)
)).

Definition encode_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx" ] |) in
    let _ := Constant.str "
    Encode a transaction. Needed because non-legacy transactions aren't RLP.
    " in
    let _ :=
        let _ :=
            let _ :=
                let _ :=
                    let _ := M.raise (| Some(M.call (|
                      M.get_name (| globals, "Exception" |),
                      make_list [
                        (* At expr: unsupported node type: JoinedStr *)
                      ],
                      make_dict []
                    |))
                    M.pure Constant.None_
                  )) |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition decode_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx" ] |) in
    let _ := Constant.str "
    Decode a transaction. Needed because non-legacy transactions aren't RLP.
    " in
    let _ :=
        let _ := M.return_ (|
          M.get_name (| globals, "tx" |)
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).
