Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.genesis".

Definition locals_stack : list Locals.t := [].

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

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_Any :
  IsImported globals "typing" "Any".
Axiom typing_imports_Dict :
  IsImported globals "typing" "Dict".
Axiom typing_imports_cast :
  IsImported globals "typing" "cast".

Axiom ethereum_imports_rlp :
  IsImported globals "ethereum" "rlp".

Axiom ethereum_base_types_imports_U64 :
  IsImported globals "ethereum.base_types" "U64".
Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes8 :
  IsImported globals "ethereum.base_types" "Bytes8".
Axiom ethereum_base_types_imports_Bytes20 :
  IsImported globals "ethereum.base_types" "Bytes20".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".
Axiom ethereum_base_types_imports_slotted_freezable :
  IsImported globals "ethereum.base_types" "slotted_freezable".

Axiom ethereum_utils_hexadecimal_imports_hex_to_bytes :
  IsImported globals "ethereum.utils.hexadecimal" "hex_to_bytes".
Axiom ethereum_utils_hexadecimal_imports_hex_to_bytes8 :
  IsImported globals "ethereum.utils.hexadecimal" "hex_to_bytes8".
Axiom ethereum_utils_hexadecimal_imports_hex_to_bytes32 :
  IsImported globals "ethereum.utils.hexadecimal" "hex_to_bytes32".
Axiom ethereum_utils_hexadecimal_imports_hex_to_u256 :
  IsImported globals "ethereum.utils.hexadecimal" "hex_to_u256".
Axiom ethereum_utils_hexadecimal_imports_hex_to_uint :
  IsImported globals "ethereum.utils.hexadecimal" "hex_to_uint".

Definition Address : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, locals_stack, "Bytes20" |)
)).

Definition GenesisConfiguration : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition get_genesis_configuration : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "genesis_file" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "genesis_str_data" ,
      M.call (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "cast" |),
          make_list [
            M.get_name (| globals, locals_stack, "bytes" |);
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "pkgutil" |), "get_data" |),
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
      |)
    |) in
    let _ := M.assign_local (|
      "genesis_data" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "json" |), "loads" |),
        make_list [
          M.get_name (| globals, locals_stack, "genesis_str_data" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "GenesisConfiguration" |),
        make_list [],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition hex_or_base_10_str_to_u256 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "balance" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    The genesis format can have balances and timestamps as either base 10
    numbers or 0x prefixed hex. This function supports both.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "balance" |), "startswith" |),
          make_list [
            Constant.str "0x"
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "hex_to_u256" |),
            make_list [
              M.get_name (| globals, locals_stack, "balance" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "U256" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "int" |),
                make_list [
                  M.get_name (| globals, locals_stack, "balance" |)
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
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "hardfork"; "chain"; "genesis" ] in
    ltac:(M.monadic (
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

    The `nonce` field is `0x42` referencing Douglas Adams' ""HitchHiker's Guide
    to the Galaxy"".

    The `extra_data` field contains the hash of block `1028201` on
    the pre-launch Olympus testnet. The creation of block `1028201` on Olympus
    marked the ""starting gun"" for Ethereum block creation. Including its hash
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
    let _ :=
      M.for_ (|
        make_tuple [ M.get_name (| globals, locals_stack, "address" |); M.get_name (| globals, locals_stack, "account" |) ],
        M.call (|
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "genesis" |), "initial_accounts" |), "items" |),
      make_list [],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "address" ,
            M.call (|
              M.get_field (| M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "utils" |), "hexadecimal" |), "hex_to_address" |),
              make_list [
                M.get_name (| globals, locals_stack, "address" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "state" |), "set_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "fork_types" |), "Account" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "int" |),
                make_list [
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "account" |), "get" |),
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
            M.get_name (| globals, locals_stack, "hex_or_base_10_str_to_u256" |),
            make_list [
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "account" |), "get" |),
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
            M.get_name (| globals, locals_stack, "hex_to_bytes" |),
            make_list [
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "account" |), "get" |),
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
          let _ :=
            M.for_ (|
              make_tuple [ M.get_name (| globals, locals_stack, "key" |); M.get_name (| globals, locals_stack, "value" |) ],
              M.call (|
      M.get_field (| M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "account" |), "get" |),
        make_list [
          Constant.str "storage";
          Constant.str "(* At expr: unsupported node type: Dict *)"
        ],
        make_dict []
      |), "items" |),
      make_list [],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "state" |), "set_storage" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "state" |);
      M.get_name (| globals, locals_stack, "address" |);
      M.call (|
        M.get_name (| globals, locals_stack, "hex_to_bytes32" |),
        make_list [
          M.get_name (| globals, locals_stack, "key" |)
        ],
        make_dict []
      |);
      M.call (|
        M.get_name (| globals, locals_stack, "hex_to_uint" |),
        make_list [
          M.get_name (| globals, locals_stack, "value" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
                M.pure Constant.None_
              )),
              ltac:(M.monadic (
                M.pure Constant.None_
              ))
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.assign_local (|
      "fields" ,
      Constant.str "(* At expr: unsupported node type: Dict *)"
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "hasattr" |),
          make_list [
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "blocks" |), "Header" |);
            Constant.str "mix_digest"
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_subscript (|
            M.get_name (| globals, locals_stack, "fields" |),
            Constant.str "mix_digest"
          |),
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "fork_types" |), "Hash32" |),
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
          M.get_subscript (|
            M.get_name (| globals, locals_stack, "fields" |),
            Constant.str "prev_randao"
          |),
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "fork_types" |), "Hash32" |),
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
          M.get_name (| globals, locals_stack, "hasattr" |),
          make_list [
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "blocks" |), "Header" |);
            Constant.str "base_fee_per_gas"
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_subscript (|
            M.get_name (| globals, locals_stack, "fields" |),
            Constant.str "base_fee_per_gas"
          |),
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
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
    let _ := M.assign_local (|
      "genesis_header" ,
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "blocks" |), "Header" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "genesis_block" ,
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "hardfork" |), "blocks" |), "Block" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |), "append" |),
    make_list [
      M.get_name (| globals, locals_stack, "genesis_block" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "chain_id" |),
      M.get_field (| M.get_name (| globals, locals_stack, "genesis" |), "chain_id" |)
    |) in
    M.pure Constant.None_)).
