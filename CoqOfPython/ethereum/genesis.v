Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Genesis Configuration
^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Functionalities and entities to obtain the genesis configurations for
different chains.
".

(* At top_level_stmt: unsupported node type: Import *)

(* At top_level_stmt: unsupported node type: Import *)

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require typing.
Axiom typing_Any :
  IsGlobalAlias globals typing.globals "Any".
Axiom typing_Dict :
  IsGlobalAlias globals typing.globals "Dict".
Axiom typing_cast :
  IsGlobalAlias globals typing.globals "cast".

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
Axiom ethereum_base_types_Bytes8 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes8".
Axiom ethereum_base_types_Bytes20 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes20".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".
Axiom ethereum_base_types_slotted_freezable :
  IsGlobalAlias globals ethereum.base_types.globals "slotted_freezable".

Require ethereum.utils.hexadecimal.
Axiom ethereum_utils_hexadecimal_hex_to_bytes :
  IsGlobalAlias globals ethereum.utils.hexadecimal.globals "hex_to_bytes".
Axiom ethereum_utils_hexadecimal_hex_to_bytes8 :
  IsGlobalAlias globals ethereum.utils.hexadecimal.globals "hex_to_bytes8".
Axiom ethereum_utils_hexadecimal_hex_to_bytes32 :
  IsGlobalAlias globals ethereum.utils.hexadecimal.globals "hex_to_bytes32".
Axiom ethereum_utils_hexadecimal_hex_to_u256 :
  IsGlobalAlias globals ethereum.utils.hexadecimal.globals "hex_to_u256".
Axiom ethereum_utils_hexadecimal_hex_to_uint :
  IsGlobalAlias globals ethereum.utils.hexadecimal.globals "hex_to_uint".

Definition Address : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, "Bytes20" |)
)).

Definition GenesisConfiguration : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition get_genesis_configuration : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "genesis_file" ] |) in
    let _ := Constant.str "
    Obtain the genesis configuration from the given genesis json file.

    The genesis file should be present in the `assets` directory.

    Parameters
    ----------
    genesis_file :
        The json file which contains the parameters for the genesis block
        and the pre-sale allocation data.

    Returns
    -------
    configuration : `GenesisConfiguration`
        The genesis configuration obtained from the json genesis file.
    " in
    let genesis_str_data :=
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, "cast" |),
          make_list [
            M.get_name (| globals, "bytes" |);
            M.call (|
              M.get_field (| M.get_name (| globals, "pkgutil" |), "get_data" |),
              make_list [
                Constant.str "ethereum";
                Constant.str "(* At expr: unsupported node type: JoinedStr *)"
              ],
              make_dict []
            |)
          ],
          make_dict []
        |), "decode" |),
        make_list [],
        make_dict []
      |) in
    let genesis_data :=
      M.call (|
        M.get_field (| M.get_name (| globals, "json" |), "loads" |),
        make_list [
          M.get_name (| globals, "genesis_str_data" |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "GenesisConfiguration" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition hex_or_base_10_str_to_u256 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "balance" ] |) in
    let _ := Constant.str "
    The genesis format can have balances and timestamps as either base 10
    numbers or 0x prefixed hex. This function supports both.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_field (| M.get_name (| globals, "balance" |), "startswith" |),
          make_list [
            Constant.str "0x"
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "hex_to_u256" |),
            make_list [
              M.get_name (| globals, "balance" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "U256" |),
            make_list [
              M.call (|
                M.get_name (| globals, "int" |),
                make_list [
                  M.get_name (| globals, "balance" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition add_genesis_block : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "hardfork"; "chain"; "genesis" ] |) in
    let _ := Constant.str "
    Adds the genesis block to an empty blockchain.

    The genesis block is an entirely sui generis block (unique) that is not
    governed by the general rules applying to all other Ethereum blocks.
    Instead, the only consensus requirement is that it must be identical to
    the block added by this function.

    The mainnet genesis configuration was originally created using the
    `mk_genesis_block.py` script. It is long since defunct, but is still
    available at https://github.com/ethereum/genesis_block_generator.

    The initial state is populated with balances based on the Ethereum presale
    that happened on the Bitcoin blockchain. Additional Ether worth 1.98% of
    the presale was given to the foundation.

    The `state_root` is set to the root of the initial state. The `gas_limit`
    and `difficulty` are set to suitable starting values. In particular the
    low gas limit made sending transactions impossible in the early stages of
    Frontier.

    The `nonce` field is `0x42` referencing Douglas Adams' """HitchHiker's Guide
    to the Galaxy""".

    The `extra_data` field contains the hash of block `1028201` on
    the pre-launch Olympus testnet. The creation of block `1028201` on Olympus
    marked the """starting gun""" for Ethereum block creation. Including its hash
    in the genesis block ensured a fair launch of the Ethereum mining process.

    The remaining fields are set to appropriate default values.

    On testnets the genesis configuration usually allocates 1 wei to addresses
    `0x00` to `0xFF` to avoid edgecases around precompiles being created or
    cleared (by EIP 161).

    Parameters
    ----------
    hardfork:
        The module containing the initial hardfork
    chain :
        An empty `Blockchain` object.
    genesis :
        The genesis configuration to use.
    " in
    For make_tuple [ M.get_name (| globals, "address" |); M.get_name (| globals, "account" |) ] in M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "genesis" |), "initial_accounts" |), "items" |),
    make_list [],
    make_dict []
  |) do
      let address :=
        M.call (|
          M.get_field (| M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "utils" |), "hexadecimal" |), "hex_to_address" |),
          make_list [
            M.get_name (| globals, "address" |)
          ],
          make_dict []
        |) in
      let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "state" |), "set_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, "chain" |), "state" |);
      M.get_name (| globals, "address" |);
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "fork_types" |), "Account" |),
        make_list [
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.call (|
                M.get_name (| globals, "int" |),
                make_list [
                  M.call (|
                    M.get_field (| M.get_name (| globals, "account" |), "get" |),
                    make_list [
                      Constant.str "nonce";
                      Constant.str "0"
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, "hex_or_base_10_str_to_u256" |),
            make_list [
              M.call (|
                M.get_field (| M.get_name (| globals, "account" |), "get" |),
                make_list [
                  Constant.str "balance";
                  Constant.int 0
                ],
                make_dict []
              |)
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, "hex_to_bytes" |),
            make_list [
              M.call (|
                M.get_field (| M.get_name (| globals, "account" |), "get" |),
                make_list [
                  Constant.str "code";
                  Constant.str "0x"
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
      For make_tuple [ M.get_name (| globals, "key" |); M.get_name (| globals, "value" |) ] in M.call (|
    M.get_field (| M.call (|
      M.get_field (| M.get_name (| globals, "account" |), "get" |),
      make_list [
        Constant.str "storage";
        {}
      ],
      make_dict []
    |), "items" |),
    make_list [],
    make_dict []
  |) do
        let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "state" |), "set_storage" |),
    make_list [
      M.get_field (| M.get_name (| globals, "chain" |), "state" |);
      M.get_name (| globals, "address" |);
      M.call (|
        M.get_name (| globals, "hex_to_bytes32" |),
        make_list [
          M.get_name (| globals, "key" |)
        ],
        make_dict []
      |);
      M.call (|
        M.get_name (| globals, "hex_to_uint" |),
        make_list [
          M.get_name (| globals, "value" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
      EndFor.
    EndFor.
    let fields :=
      {Constant.str "parent_hash": M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "fork_types" |), "Hash32" |),
        make_list [
          BinOp.mult (|
            Constant.bytes "00",
            Constant.int 32
          |)
        ],
        make_dict []
      |), Constant.str "ommers_hash": M.call (|
        M.get_field (| M.get_name (| globals, "rlp" |), "rlp_hash" |),
        make_list [
          make_tuple [  ]
        ],
        make_dict []
      |), Constant.str "coinbase": M.call (|
        M.get_name (| globals, "Address" |),
        make_list [
          BinOp.mult (|
            Constant.bytes "00",
            Constant.int 20
          |)
        ],
        make_dict []
      |), Constant.str "state_root": M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "state" |), "state_root" |),
        make_list [
          M.get_field (| M.get_name (| globals, "chain" |), "state" |)
        ],
        make_dict []
      |), Constant.str "transactions_root": M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "trie" |), "root" |),
        make_list [
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "trie" |), "Trie" |),
            make_list [
              Constant.bool false;
              Constant.None_
            ],
            make_dict []
          |)
        ],
        make_dict []
      |), Constant.str "receipt_root": M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "trie" |), "root" |),
        make_list [
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "trie" |), "Trie" |),
            make_list [
              Constant.bool false;
              Constant.None_
            ],
            make_dict []
          |)
        ],
        make_dict []
      |), Constant.str "bloom": M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "fork_types" |), "Bloom" |),
        make_list [
          BinOp.mult (|
            Constant.bytes "00",
            Constant.int 256
          |)
        ],
        make_dict []
      |), Constant.str "difficulty": M.get_field (| M.get_name (| globals, "genesis" |), "difficulty" |), Constant.str "number": M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |), Constant.str "gas_limit": M.get_field (| M.get_name (| globals, "genesis" |), "gas_limit" |), Constant.str "gas_used": M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |), Constant.str "timestamp": M.get_field (| M.get_name (| globals, "genesis" |), "timestamp" |), Constant.str "extra_data": M.get_field (| M.get_name (| globals, "genesis" |), "extra_data" |), Constant.str "nonce": M.get_field (| M.get_name (| globals, "genesis" |), "nonce" |)} in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "hasattr" |),
          make_list [
            M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "blocks" |), "Header" |);
            Constant.str "mix_digest"
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_subscript (| M.get_name (| globals, "fields" |), Constant.str "mix_digest" |),
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "fork_types" |), "Hash32" |),
            make_list [
              BinOp.mult (|
                Constant.bytes "00",
                Constant.int 32
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign (|
          M.get_subscript (| M.get_name (| globals, "fields" |), Constant.str "prev_randao" |),
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "fork_types" |), "Hash32" |),
            make_list [
              BinOp.mult (|
                Constant.bytes "00",
                Constant.int 32
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "hasattr" |),
          make_list [
            M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "blocks" |), "Header" |);
            Constant.str "base_fee_per_gas"
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_subscript (| M.get_name (| globals, "fields" |), Constant.str "base_fee_per_gas" |),
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              BinOp.pow (|
                Constant.int 10,
                Constant.int 9
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let genesis_header :=
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "blocks" |), "Header" |),
        make_list [],
        make_dict []
      |) in
    let genesis_block :=
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "hardfork" |), "blocks" |), "Block" |),
        make_list [],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "chain" |), "blocks" |), "append" |),
    make_list [
      M.get_name (| globals, "genesis_block" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "chain" |), "chain_id" |),
      M.get_field (| M.get_name (| globals, "genesis" |), "chain_id" |)
    |) in
    M.pure Constant.None_)).
