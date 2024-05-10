Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.gray_glacier.transactions".

Definition expr_1 : Value.t :=
  Constant.str "
Transactions are atomic units of work created externally to Ethereum and
submitted to be executed. If Ethereum is viewed as a state machine,
transactions are the events that move between states.
".

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Axiom ethereum_imports_rlp :
  IsImported globals "ethereum" "rlp".

Axiom ethereum_base_types_imports_U64 :
  IsImported globals "ethereum.base_types" "U64".
Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".
Axiom ethereum_base_types_imports_Bytes32 :
  IsImported globals "ethereum.base_types" "Bytes32".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".
Axiom ethereum_base_types_imports_slotted_freezable :
  IsImported globals "ethereum.base_types" "slotted_freezable".

Axiom ethereum_exceptions_imports_InvalidBlock :
  IsImported globals "ethereum.exceptions" "InvalidBlock".

Axiom ethereum_gray_glacier_fork_types_imports_Address :
  IsImported globals "ethereum.gray_glacier.fork_types" "Address".

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
  M.get_subscript (|
    M.get_name (| globals, "Union" |),
    make_tuple [ M.get_name (| globals, "LegacyTransaction" |); M.get_name (| globals, "AccessListTransaction" |); M.get_name (| globals, "FeeMarketTransaction" |) ]
  |)
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
                let _ := M.raise (| Some (M.call (|
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
              M.get_subscript (|
                M.get_name (| globals, "tx" |),
                Constant.int 0
              |),
              Constant.int 1
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.call (|
                M.get_field (| M.get_name (| globals, "rlp" |), "decode_to" |),
                make_list [
                  M.get_name (| globals, "AccessListTransaction" |);
                  M.slice (|
                    M.get_name (| globals, "tx" |),
                    Constant.int 1,
                    Constant.None_,
                    Constant.None_
                  |)
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
                  M.get_subscript (|
                    M.get_name (| globals, "tx" |),
                    Constant.int 0
                  |),
                  Constant.int 2
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "rlp" |), "decode_to" |),
                    make_list [
                      M.get_name (| globals, "FeeMarketTransaction" |);
                      M.slice (|
                        M.get_name (| globals, "tx" |),
                        Constant.int 1,
                        Constant.None_,
                        Constant.None_
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, "InvalidBlock" |)) |) in
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
