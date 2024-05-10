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

Require ethereum.__init__.
Axiom ethereum___init___rlp :
  IsGlobalAlias globals ethereum.__init__.globals "rlp".

Require ethereum.base_types.
Axiom ethereum_base_types_U64 :
  IsGlobalAlias globals ethereum.base_types.globals "U64".
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".
Axiom ethereum_base_types_Bytes0 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes0".
Axiom ethereum_base_types_Bytes32 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes32".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".
Axiom ethereum_base_types_slotted_freezable :
  IsGlobalAlias globals ethereum.base_types.globals "slotted_freezable".

Require ethereum.exceptions.
Axiom ethereum_exceptions_InvalidBlock :
  IsGlobalAlias globals ethereum.exceptions.globals "InvalidBlock".

Require ethereum.gray_glacier.fork_types.
Axiom ethereum_gray_glacier_fork_types_Address :
  IsGlobalAlias globals ethereum.gray_glacier.fork_types.globals "Address".

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

Definition Transaction : Value.t := M.run ltac:(M.monadic (
  M.get_subscript (| M.get_name (| globals, "Union" |), make_tuple [ M.get_name (| globals, "LegacyTransaction" |); M.get_name (| globals, "AccessListTransaction" |); M.get_name (| globals, "FeeMarketTransaction" |) ] |)
)).

Definition encode_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx" ] |) in
    let _ := Constant.str "
    Encode a transaction. Needed because non-legacy transactions aren't RLP.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "isinstance" |),
          make_list [
            M.get_name (| globals, "tx" |);
            M.get_name (| globals, "LegacyTransaction" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, "tx" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, "isinstance" |),
              make_list [
                M.get_name (| globals, "tx" |);
                M.get_name (| globals, "AccessListTransaction" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              BinOp.add (|
                Constant.bytes "01",
                M.call (|
                  M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
                  make_list [
                    M.get_name (| globals, "tx" |)
                  ],
                  make_dict []
                |)
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                M.call (|
                  M.get_name (| globals, "isinstance" |),
                  make_list [
                    M.get_name (| globals, "tx" |);
                    M.get_name (| globals, "FeeMarketTransaction" |)
                  ],
                  make_dict []
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (|
                  BinOp.add (|
                    Constant.bytes "02",
                    M.call (|
                      M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
                      make_list [
                        M.get_name (| globals, "tx" |)
                      ],
                      make_dict []
                    |)
                  |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ := M.raise (| Some(M.call (|
                  M.get_name (| globals, "Exception" |),
                  make_list [
                    Constant.str "(* At expr: unsupported node type: JoinedStr *)"
                  ],
                  make_dict []
                |)) |) in
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
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "isinstance" |),
          make_list [
            M.get_name (| globals, "tx" |);
            M.get_name (| globals, "Bytes" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_subscript (| M.get_name (| globals, "tx" |), Constant.int 0 |),
              Constant.int 1
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.call (|
                M.get_field (| M.get_name (| globals, "rlp" |), "decode_to" |),
                make_list [
                  M.get_name (| globals, "AccessListTransaction" |);
                  M.get_subscript (| M.get_name (| globals, "tx" |), M.slice (| Constant.int 1, Constant.None_ |) |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.eq (|
                  M.get_subscript (| M.get_name (| globals, "tx" |), Constant.int 0 |),
                  Constant.int 2
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "rlp" |), "decode_to" |),
                    make_list [
                      M.get_name (| globals, "FeeMarketTransaction" |);
                      M.get_subscript (| M.get_name (| globals, "tx" |), M.slice (| Constant.int 1, Constant.None_ |) |)
                    ],
                    make_dict []
                  |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ := M.raise (| Some(M.get_name (| globals, "InvalidBlock" |)) |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, "tx" |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).
