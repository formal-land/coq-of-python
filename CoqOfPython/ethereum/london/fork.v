Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.london.fork".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Specification
^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Entry point for the Ethereum specification.
".

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_List :
  IsImported globals "typing" "List".
Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Set :
  IsImported globals "typing" "Set".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".

Axiom ethereum_base_types_imports_Bytes0 :
  IsImported globals "ethereum.base_types" "Bytes0".

Axiom ethereum_crypto_elliptic_curve_imports_SECP256K1N :
  IsImported globals "ethereum.crypto.elliptic_curve" "SECP256K1N".
Axiom ethereum_crypto_elliptic_curve_imports_secp256k1_recover :
  IsImported globals "ethereum.crypto.elliptic_curve" "secp256k1_recover".

Axiom ethereum_crypto_hash_imports_Hash32 :
  IsImported globals "ethereum.crypto.hash" "Hash32".
Axiom ethereum_crypto_hash_imports_keccak256 :
  IsImported globals "ethereum.crypto.hash" "keccak256".

Axiom ethereum_ethash_imports_dataset_size :
  IsImported globals "ethereum.ethash" "dataset_size".
Axiom ethereum_ethash_imports_generate_cache :
  IsImported globals "ethereum.ethash" "generate_cache".
Axiom ethereum_ethash_imports_hashimoto_light :
  IsImported globals "ethereum.ethash" "hashimoto_light".

Axiom ethereum_exceptions_imports_InvalidBlock :
  IsImported globals "ethereum.exceptions" "InvalidBlock".

Axiom ethereum_imports_rlp :
  IsImported globals "ethereum" "rlp".

Axiom ethereum_base_types_imports_U64 :
  IsImported globals "ethereum.base_types" "U64".
Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_U256_CEIL_VALUE :
  IsImported globals "ethereum.base_types" "U256_CEIL_VALUE".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Axiom ethereum_london_imports_FORK_CRITERIA :
  IsImported globals "ethereum.london" "FORK_CRITERIA".
Axiom ethereum_london_imports_vm :
  IsImported globals "ethereum.london" "vm".

Axiom ethereum_london_blocks_imports_Block :
  IsImported globals "ethereum.london.blocks" "Block".
Axiom ethereum_london_blocks_imports_Header :
  IsImported globals "ethereum.london.blocks" "Header".
Axiom ethereum_london_blocks_imports_Log :
  IsImported globals "ethereum.london.blocks" "Log".
Axiom ethereum_london_blocks_imports_Receipt :
  IsImported globals "ethereum.london.blocks" "Receipt".

Axiom ethereum_london_bloom_imports_logs_bloom :
  IsImported globals "ethereum.london.bloom" "logs_bloom".

Axiom ethereum_london_fork_types_imports_Address :
  IsImported globals "ethereum.london.fork_types" "Address".
Axiom ethereum_london_fork_types_imports_Bloom :
  IsImported globals "ethereum.london.fork_types" "Bloom".
Axiom ethereum_london_fork_types_imports_Root :
  IsImported globals "ethereum.london.fork_types" "Root".

Axiom ethereum_london_state_imports_State :
  IsImported globals "ethereum.london.state" "State".
Axiom ethereum_london_state_imports_account_exists_and_is_empty :
  IsImported globals "ethereum.london.state" "account_exists_and_is_empty".
Axiom ethereum_london_state_imports_create_ether :
  IsImported globals "ethereum.london.state" "create_ether".
Axiom ethereum_london_state_imports_destroy_account :
  IsImported globals "ethereum.london.state" "destroy_account".
Axiom ethereum_london_state_imports_get_account :
  IsImported globals "ethereum.london.state" "get_account".
Axiom ethereum_london_state_imports_increment_nonce :
  IsImported globals "ethereum.london.state" "increment_nonce".
Axiom ethereum_london_state_imports_set_account_balance :
  IsImported globals "ethereum.london.state" "set_account_balance".
Axiom ethereum_london_state_imports_state_root :
  IsImported globals "ethereum.london.state" "state_root".

Axiom ethereum_london_transactions_imports_TX_ACCESS_LIST_ADDRESS_COST :
  IsImported globals "ethereum.london.transactions" "TX_ACCESS_LIST_ADDRESS_COST".
Axiom ethereum_london_transactions_imports_TX_ACCESS_LIST_STORAGE_KEY_COST :
  IsImported globals "ethereum.london.transactions" "TX_ACCESS_LIST_STORAGE_KEY_COST".
Axiom ethereum_london_transactions_imports_TX_BASE_COST :
  IsImported globals "ethereum.london.transactions" "TX_BASE_COST".
Axiom ethereum_london_transactions_imports_TX_CREATE_COST :
  IsImported globals "ethereum.london.transactions" "TX_CREATE_COST".
Axiom ethereum_london_transactions_imports_TX_DATA_COST_PER_NON_ZERO :
  IsImported globals "ethereum.london.transactions" "TX_DATA_COST_PER_NON_ZERO".
Axiom ethereum_london_transactions_imports_TX_DATA_COST_PER_ZERO :
  IsImported globals "ethereum.london.transactions" "TX_DATA_COST_PER_ZERO".
Axiom ethereum_london_transactions_imports_AccessListTransaction :
  IsImported globals "ethereum.london.transactions" "AccessListTransaction".
Axiom ethereum_london_transactions_imports_FeeMarketTransaction :
  IsImported globals "ethereum.london.transactions" "FeeMarketTransaction".
Axiom ethereum_london_transactions_imports_LegacyTransaction :
  IsImported globals "ethereum.london.transactions" "LegacyTransaction".
Axiom ethereum_london_transactions_imports_Transaction :
  IsImported globals "ethereum.london.transactions" "Transaction".
Axiom ethereum_london_transactions_imports_decode_transaction :
  IsImported globals "ethereum.london.transactions" "decode_transaction".
Axiom ethereum_london_transactions_imports_encode_transaction :
  IsImported globals "ethereum.london.transactions" "encode_transaction".

Axiom ethereum_london_trie_imports_Trie :
  IsImported globals "ethereum.london.trie" "Trie".
Axiom ethereum_london_trie_imports_root :
  IsImported globals "ethereum.london.trie" "root".
Axiom ethereum_london_trie_imports_trie_set :
  IsImported globals "ethereum.london.trie" "trie_set".

Axiom ethereum_london_utils_message_imports_prepare_message :
  IsImported globals "ethereum.london.utils.message" "prepare_message".

Axiom ethereum_london_vm_interpreter_imports_process_message_call :
  IsImported globals "ethereum.london.vm.interpreter" "process_message_call".

Definition BLOCK_REWARD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "U256" |),
    make_list [
      BinOp.mult (|
        Constant.int 2,
        BinOp.pow (|
          Constant.int 10,
          Constant.int 18
        |)
      |)
    ],
    make_dict []
  |)
)).

Definition BASE_FEE_MAX_CHANGE_DENOMINATOR : Value.t := M.run ltac:(M.monadic (
  Constant.int 8
)).

Definition ELASTICITY_MULTIPLIER : Value.t := M.run ltac:(M.monadic (
  Constant.int 2
)).

Definition GAS_LIMIT_ADJUSTMENT_FACTOR : Value.t := M.run ltac:(M.monadic (
  Constant.int 1024
)).

Definition GAS_LIMIT_MINIMUM : Value.t := M.run ltac:(M.monadic (
  Constant.int 5000
)).

Definition MINIMUM_DIFFICULTY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Uint" |),
    make_list [
      Constant.int 131072
    ],
    make_dict []
  |)
)).

Definition INITIAL_BASE_FEE : Value.t := M.run ltac:(M.monadic (
  Constant.int 1000000000
)).

Definition MAX_OMMER_DEPTH : Value.t := M.run ltac:(M.monadic (
  Constant.int 6
)).

Definition BOMB_DELAY_BLOCKS : Value.t := M.run ltac:(M.monadic (
  Constant.int 9700000
)).

Definition EMPTY_OMMER_HASH : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "keccak256" |),
    make_list [
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
        make_list [
          make_list []
        ],
        make_dict []
      |)
    ],
    make_dict []
  |)
)).

Definition BlockChain : Value.t := make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition apply_fork : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "old" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Transforms the state from the previous hard fork (`old`) into the block
    chain object for this hard fork and returns it.

    When forks need to implement an irregular state transition, this function
    is used to handle the irregularity. See the :ref:`DAO Fork <dao-fork>` for
    an example.

    Parameters
    ----------
    old :
        Previous block chain object.

    Returns
    -------
    new : `BlockChain`
        Upgraded block chain object for this hard fork.
    " in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "old" |)
    |) in
    M.pure Constant.None_)).

Axiom apply_fork_in_globals :
  IsInGlobals globals "apply_fork" (make_function apply_fork).

Definition get_last_256_block_hashes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "chain" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Obtain the list of hashes of the previous 256 blocks in order of
    increasing block number.

    This function will return less hashes for the first 256 blocks.

    The ``BLOCKHASH`` opcode needs to access the latest hashes on the chain,
    therefore this function retrieves them.

    Parameters
    ----------
    chain :
        History and current state.

    Returns
    -------
    recent_block_hashes : `List[Hash32]`
        Hashes of the recent 256 blocks in order of increasing block number.
    " in
    let _ := M.assign_local (|
      "recent_blocks" ,
      M.slice (|
        M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |),
        UnOp.sub (| Constant.int 255 |),
        Constant.None_,
        Constant.None_
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "recent_blocks" |)
            ],
            make_dict []
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          make_list []
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "recent_block_hashes" ,
      make_list []
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "block" |),
        M.get_name (| globals, locals_stack, "recent_blocks" |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "prev_block_hash" ,
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "parent_hash" |)
          |) in
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "recent_block_hashes" |), "append" |),
    make_list [
      M.get_name (| globals, locals_stack, "prev_block_hash" |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.assign_local (|
      "most_recent_block_hash" ,
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
            make_list [
              M.get_field (| M.get_subscript (|
                M.get_name (| globals, locals_stack, "recent_blocks" |),
                UnOp.sub (| Constant.int 1 |)
              |), "header" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "recent_block_hashes" |), "append" |),
    make_list [
      M.get_name (| globals, locals_stack, "most_recent_block_hash" |)
    ],
    make_dict []
  |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "recent_block_hashes" |)
    |) in
    M.pure Constant.None_)).

Axiom get_last_256_block_hashes_in_globals :
  IsInGlobals globals "get_last_256_block_hashes" (make_function get_last_256_block_hashes).

Definition state_transition : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "chain"; "block" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Attempts to apply a block to an existing block chain.

    All parts of the block's contents need to be verified before being added
    to the chain. Blocks are verified by ensuring that the contents of the
    block make logical sense with the contents of the parent block. The
    information in the block's header must also match the corresponding
    information in the block.

    To implement Ethereum, in theory clients are only required to store the
    most recent 255 blocks of the chain since as far as execution is
    concerned, only those blocks are accessed. Practically, however, clients
    should store more blocks to handle reorgs.

    Parameters
    ----------
    chain :
        History and current state.
    block :
        Block to apply to `chain`.
    " in
    let _ := M.assign_local (|
      "parent_header" ,
      M.get_field (| M.get_subscript (|
        M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |),
        UnOp.sub (| Constant.int 1 |)
      |), "header" |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "validate_header" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |);
      M.get_name (| globals, locals_stack, "parent_header" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "validate_ommers" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "block" |), "ommers" |);
      M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |);
      M.get_name (| globals, locals_stack, "chain" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "apply_body_output" ,
      M.call (|
        M.get_name (| globals, locals_stack, "apply_body" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "state" |);
          M.call (|
            M.get_name (| globals, locals_stack, "get_last_256_block_hashes" |),
            make_list [
              M.get_name (| globals, locals_stack, "chain" |)
            ],
            make_dict []
          |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "coinbase" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "number" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "base_fee_per_gas" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "gas_limit" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "timestamp" |);
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "difficulty" |);
          M.get_field (| M.get_name (| globals, locals_stack, "block" |), "transactions" |);
          M.get_field (| M.get_name (| globals, locals_stack, "block" |), "ommers" |);
          M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "chain_id" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "apply_body_output" |), "block_gas_used" |),
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "gas_used" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "apply_body_output" |), "transactions_root" |),
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "transactions_root" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "apply_body_output" |), "state_root" |),
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "state_root" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "apply_body_output" |), "receipt_root" |),
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "receipt_root" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "apply_body_output" |), "block_logs_bloom" |),
          M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "block" |), "header" |), "bloom" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |), "append" |),
    make_list [
      M.get_name (| globals, locals_stack, "block" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |)
            ],
            make_dict []
          |),
          Constant.int 255
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |),
          M.slice (|
            M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |),
            UnOp.sub (| Constant.int 255 |),
            Constant.None_,
            Constant.None_
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom state_transition_in_globals :
  IsInGlobals globals "state_transition" (make_function state_transition).

Definition calculate_base_fee_per_gas : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "block_gas_limit"; "parent_gas_limit"; "parent_gas_used"; "parent_base_fee_per_gas"; "is_fork_block" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Calculates the base fee per gas for the block.

    Parameters
    ----------
    block_gas_limit :
        Gas limit of the block for which the base fee is being calculated.
    parent_gas_limit :
        Gas limit of the parent block.
    parent_gas_used :
        Gas used in the parent block.
    parent_base_fee_per_gas :
        Base fee per gas of the parent block.
    is_fork_block :
        Whether the block is the fork block.

    Returns
    -------
    base_fee_per_gas : `Uint`
        Base fee per gas for the block.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.get_name (| globals, locals_stack, "is_fork_block" |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_name (| globals, locals_stack, "INITIAL_BASE_FEE" |)
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
      "parent_gas_target" ,
      BinOp.floor_div (|
        M.get_name (| globals, locals_stack, "parent_gas_limit" |),
        M.get_name (| globals, locals_stack, "ELASTICITY_MULTIPLIER" |)
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        UnOp.not (| M.call (|
          M.get_name (| globals, locals_stack, "check_gas_limit" |),
          make_list [
            M.get_name (| globals, locals_stack, "block_gas_limit" |);
            M.get_name (| globals, locals_stack, "parent_gas_limit" |)
          ],
          make_dict []
        |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "parent_gas_used" |),
          M.get_name (| globals, locals_stack, "parent_gas_target" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "expected_base_fee_per_gas" ,
          M.get_name (| globals, locals_stack, "parent_base_fee_per_gas" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt (|
              M.get_name (| globals, locals_stack, "parent_gas_used" |),
              M.get_name (| globals, locals_stack, "parent_gas_target" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "gas_used_delta" ,
              BinOp.sub (|
                M.get_name (| globals, locals_stack, "parent_gas_used" |),
                M.get_name (| globals, locals_stack, "parent_gas_target" |)
              |)
            |) in
            let _ := M.assign_local (|
              "parent_fee_gas_delta" ,
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "parent_base_fee_per_gas" |),
                M.get_name (| globals, locals_stack, "gas_used_delta" |)
              |)
            |) in
            let _ := M.assign_local (|
              "target_fee_gas_delta" ,
              BinOp.floor_div (|
                M.get_name (| globals, locals_stack, "parent_fee_gas_delta" |),
                M.get_name (| globals, locals_stack, "parent_gas_target" |)
              |)
            |) in
            let _ := M.assign_local (|
              "base_fee_per_gas_delta" ,
              M.call (|
                M.get_name (| globals, locals_stack, "max" |),
                make_list [
                  BinOp.floor_div (|
                    M.get_name (| globals, locals_stack, "target_fee_gas_delta" |),
                    M.get_name (| globals, locals_stack, "BASE_FEE_MAX_CHANGE_DENOMINATOR" |)
                  |);
                  Constant.int 1
                ],
                make_dict []
              |)
            |) in
            let _ := M.assign_local (|
              "expected_base_fee_per_gas" ,
              BinOp.add (|
                M.get_name (| globals, locals_stack, "parent_base_fee_per_gas" |),
                M.get_name (| globals, locals_stack, "base_fee_per_gas_delta" |)
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.assign_local (|
              "gas_used_delta" ,
              BinOp.sub (|
                M.get_name (| globals, locals_stack, "parent_gas_target" |),
                M.get_name (| globals, locals_stack, "parent_gas_used" |)
              |)
            |) in
            let _ := M.assign_local (|
              "parent_fee_gas_delta" ,
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "parent_base_fee_per_gas" |),
                M.get_name (| globals, locals_stack, "gas_used_delta" |)
              |)
            |) in
            let _ := M.assign_local (|
              "target_fee_gas_delta" ,
              BinOp.floor_div (|
                M.get_name (| globals, locals_stack, "parent_fee_gas_delta" |),
                M.get_name (| globals, locals_stack, "parent_gas_target" |)
              |)
            |) in
            let _ := M.assign_local (|
              "base_fee_per_gas_delta" ,
              BinOp.floor_div (|
                M.get_name (| globals, locals_stack, "target_fee_gas_delta" |),
                M.get_name (| globals, locals_stack, "BASE_FEE_MAX_CHANGE_DENOMINATOR" |)
              |)
            |) in
            let _ := M.assign_local (|
              "expected_base_fee_per_gas" ,
              BinOp.sub (|
                M.get_name (| globals, locals_stack, "parent_base_fee_per_gas" |),
                M.get_name (| globals, locals_stack, "base_fee_per_gas_delta" |)
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.get_name (| globals, locals_stack, "expected_base_fee_per_gas" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom calculate_base_fee_per_gas_in_globals :
  IsInGlobals globals "calculate_base_fee_per_gas" (make_function calculate_base_fee_per_gas).

Definition validate_header : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "header"; "parent_header" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Verifies a block header.

    In order to consider a block's header valid, the logic for the
    quantities in the header should match the logic for the block itself.
    For example the header timestamp should be greater than the block's parent
    timestamp because the block was created *after* the parent block.
    Additionally, the block's number should be directly following the parent
    block's number since it is the next block in the sequence.

    Parameters
    ----------
    header :
        Header to check for correctness.
    parent_header :
        Parent Header of the header to check for correctness
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "gas_used" |),
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "gas_limit" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "is_fork_block" ,
      Compare.eq (|
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "number" |),
        M.get_field (| M.get_name (| globals, locals_stack, "FORK_CRITERIA" |), "block_number" |)
      |)
    |) in
    let _ := M.assign_local (|
      "expected_base_fee_per_gas" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_base_fee_per_gas" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "gas_limit" |);
          M.get_field (| M.get_name (| globals, locals_stack, "parent_header" |), "gas_limit" |);
          M.get_field (| M.get_name (| globals, locals_stack, "parent_header" |), "gas_used" |);
          M.get_field (| M.get_name (| globals, locals_stack, "parent_header" |), "base_fee_per_gas" |);
          M.get_name (| globals, locals_stack, "is_fork_block" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_name (| globals, locals_stack, "expected_base_fee_per_gas" |),
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "base_fee_per_gas" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "parent_has_ommers" ,
      Compare.not_eq (|
        M.get_field (| M.get_name (| globals, locals_stack, "parent_header" |), "ommers_hash" |),
        M.get_name (| globals, locals_stack, "EMPTY_OMMER_HASH" |)
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "timestamp" |),
          M.get_field (| M.get_name (| globals, locals_stack, "parent_header" |), "timestamp" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "number" |),
          BinOp.add (|
            M.get_field (| M.get_name (| globals, locals_stack, "parent_header" |), "number" |),
            Constant.int 1
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "header" |), "extra_data" |)
            ],
            make_dict []
          |),
          Constant.int 32
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "block_difficulty" ,
      M.call (|
        M.get_name (| globals, locals_stack, "calculate_block_difficulty" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "number" |);
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "timestamp" |);
          M.get_field (| M.get_name (| globals, locals_stack, "parent_header" |), "timestamp" |);
          M.get_field (| M.get_name (| globals, locals_stack, "parent_header" |), "difficulty" |);
          M.get_name (| globals, locals_stack, "parent_has_ommers" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "difficulty" |),
          M.get_name (| globals, locals_stack, "block_difficulty" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "block_parent_hash" ,
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
            make_list [
              M.get_name (| globals, locals_stack, "parent_header" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "parent_hash" |),
          M.get_name (| globals, locals_stack, "block_parent_hash" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "validate_proof_of_work" |),
    make_list [
      M.get_name (| globals, locals_stack, "header" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Axiom validate_header_in_globals :
  IsInGlobals globals "validate_header" (make_function validate_header).

Definition generate_header_hash_for_pow : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "header" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Generate rlp hash of the header which is to be used for Proof-of-Work
    verification.

    In other words, the PoW artefacts `mix_digest` and `nonce` are ignored
    while calculating this hash.

    A particular PoW is valid for a single hash, that hash is computed by
    this function. The `nonce` and `mix_digest` are omitted from this hash
    because they are being changed by miners in their search for a sufficient
    proof-of-work.

    Parameters
    ----------
    header :
        The header object for which the hash is to be generated.

    Returns
    -------
    hash : `Hash32`
        The PoW valid rlp hash of the passed in header.
    " in
    let _ := M.assign_local (|
      "header_data_without_pow_artefacts" ,
      make_list [
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "parent_hash" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "ommers_hash" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "coinbase" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "state_root" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "transactions_root" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "receipt_root" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "bloom" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "difficulty" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "number" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "gas_limit" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "gas_used" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "timestamp" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "extra_data" |);
        M.get_field (| M.get_name (| globals, locals_stack, "header" |), "base_fee_per_gas" |)
      ]
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "rlp_hash" |),
        make_list [
          M.get_name (| globals, locals_stack, "header_data_without_pow_artefacts" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom generate_header_hash_for_pow_in_globals :
  IsInGlobals globals "generate_header_hash_for_pow" (make_function generate_header_hash_for_pow).

Definition validate_proof_of_work : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "header" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Validates the Proof of Work constraints.

    In order to verify that a miner's proof-of-work is valid for a block, a
    ``mix-digest`` and ``result`` are calculated using the ``hashimoto_light``
    hash function. The mix digest is a hash of the header and the nonce that
    is passed through and it confirms whether or not proof-of-work was done
    on the correct block. The result is the actual hash value of the block.

    Parameters
    ----------
    header :
        Header of interest.
    " in
    let _ := M.assign_local (|
      "header_hash" ,
      M.call (|
        M.get_name (| globals, locals_stack, "generate_header_hash_for_pow" |),
        make_list [
          M.get_name (| globals, locals_stack, "header" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "cache" ,
      M.call (|
        M.get_name (| globals, locals_stack, "generate_cache" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "number" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      make_tuple [ M.get_name (| globals, locals_stack, "mix_digest" |); M.get_name (| globals, locals_stack, "result" |) ],
      M.call (|
        M.get_name (| globals, locals_stack, "hashimoto_light" |),
        make_list [
          M.get_name (| globals, locals_stack, "header_hash" |);
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "nonce" |);
          M.get_name (| globals, locals_stack, "cache" |);
          M.call (|
            M.get_name (| globals, locals_stack, "dataset_size" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "header" |), "number" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_name (| globals, locals_stack, "mix_digest" |),
          M.get_field (| M.get_name (| globals, locals_stack, "header" |), "mix_digest" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
            make_list [
              M.get_name (| globals, locals_stack, "result" |)
            ],
            make_dict []
          |),
          BinOp.floor_div (|
            M.get_name (| globals, locals_stack, "U256_CEIL_VALUE" |),
            M.get_field (| M.get_name (| globals, locals_stack, "header" |), "difficulty" |)
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom validate_proof_of_work_in_globals :
  IsInGlobals globals "validate_proof_of_work" (make_function validate_proof_of_work).

Definition check_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "tx"; "base_fee_per_gas"; "gas_available"; "chain_id" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Check if the transaction is includable in the block.

    Parameters
    ----------
    tx :
        The transaction.
    base_fee_per_gas :
        The block base fee.
    gas_available :
        The gas remaining in the block.
    chain_id :
        The ID of the current chain.

    Returns
    -------
    sender_address :
        The sender of the transaction.
    effective_gas_price :
        The price to charge for gas when the transaction is executed.

    Raises
    ------
    InvalidBlock :
        If the transaction is not includable.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |),
          M.get_name (| globals, locals_stack, "gas_available" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "sender_address" ,
      M.call (|
        M.get_name (| globals, locals_stack, "recover_sender" |),
        make_list [
          M.get_name (| globals, locals_stack, "chain_id" |);
          M.get_name (| globals, locals_stack, "tx" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "tx" |);
            M.get_name (| globals, locals_stack, "FeeMarketTransaction" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (|
              M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "max_fee_per_gas" |),
              M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "max_priority_fee_per_gas" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (|
              M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "max_fee_per_gas" |),
              M.get_name (| globals, locals_stack, "base_fee_per_gas" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.assign_local (|
          "priority_fee_per_gas" ,
          M.call (|
            M.get_name (| globals, locals_stack, "min" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "max_priority_fee_per_gas" |);
              BinOp.sub (|
                M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "max_fee_per_gas" |),
                M.get_name (| globals, locals_stack, "base_fee_per_gas" |)
              |)
            ],
            make_dict []
          |)
        |) in
        let _ := M.assign_local (|
          "effective_gas_price" ,
          BinOp.add (|
            M.get_name (| globals, locals_stack, "priority_fee_per_gas" |),
            M.get_name (| globals, locals_stack, "base_fee_per_gas" |)
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (|
              M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas_price" |),
              M.get_name (| globals, locals_stack, "base_fee_per_gas" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.assign_local (|
          "effective_gas_price" ,
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas_price" |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      make_tuple [ M.get_name (| globals, locals_stack, "sender_address" |); M.get_name (| globals, locals_stack, "effective_gas_price" |) ]
    |) in
    M.pure Constant.None_)).

Axiom check_transaction_in_globals :
  IsInGlobals globals "check_transaction" (make_function check_transaction).

Definition make_receipt : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "tx"; "error"; "cumulative_gas_used"; "logs" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Make the receipt for a transaction that was executed.

    Parameters
    ----------
    tx :
        The executed transaction.
    error :
        Error in the top level frame of the transaction, if any.
    cumulative_gas_used :
        The total gas used so far in the block after the transaction was
        executed.
    logs :
        The logs produced by the transaction.

    Returns
    -------
    receipt :
        The receipt for the transaction.
    " in
    let _ := M.assign_local (|
      "receipt" ,
      M.call (|
        M.get_name (| globals, locals_stack, "Receipt" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "tx" |);
            M.get_name (| globals, locals_stack, "AccessListTransaction" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          BinOp.add (|
            Constant.bytes "01",
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
              make_list [
                M.get_name (| globals, locals_stack, "receipt" |)
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
              M.get_name (| globals, locals_stack, "isinstance" |),
              make_list [
                M.get_name (| globals, locals_stack, "tx" |);
                M.get_name (| globals, locals_stack, "FeeMarketTransaction" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              BinOp.add (|
                Constant.bytes "02",
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "receipt" |)
                  ],
                  make_dict []
                |)
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.return_ (|
              M.get_name (| globals, locals_stack, "receipt" |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom make_receipt_in_globals :
  IsInGlobals globals "make_receipt" (make_function make_receipt).

Definition ApplyBodyOutput : Value.t := make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition apply_body : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "block_hashes"; "coinbase"; "block_number"; "base_fee_per_gas"; "block_gas_limit"; "block_time"; "block_difficulty"; "transactions"; "ommers"; "chain_id" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Executes a block.

    Many of the contents of a block are stored in data structures called
    tries. There is a transactions trie which is similar to a ledger of the
    transactions stored in the current block. There is also a receipts trie
    which stores the results of executing a transaction, like the post state
    and gas used. This function creates and executes the block that is to be
    added to the chain.

    Parameters
    ----------
    state :
        Current account state.
    block_hashes :
        List of hashes of the previous 256 blocks in the order of
        increasing block number.
    coinbase :
        Address of account which receives block reward and transaction fees.
    block_number :
        Position of the block within the chain.
    base_fee_per_gas :
        Base fee per gas of within the block.
    block_gas_limit :
        Initial amount of gas available for execution in this block.
    block_time :
        Time the block was produced, measured in seconds since the epoch.
    block_difficulty :
        Difficulty of the block.
    transactions :
        Transactions included in the block.
    ommers :
        Headers of ancestor blocks which are not direct parents (formerly
        uncles.)
    chain_id :
        ID of the executing chain.

    Returns
    -------
    apply_body_output : `ApplyBodyOutput`
        Output of applying the block body to the state.
    " in
    let _ := M.assign_local (|
      "gas_available" ,
      M.get_name (| globals, locals_stack, "block_gas_limit" |)
    |) in
(* At stmt: unsupported node type: AnnAssign *)
(* At stmt: unsupported node type: AnnAssign *)
(* At stmt: unsupported node type: AnnAssign *)
    let _ :=
      M.for_ (|
        make_tuple [ M.get_name (| globals, locals_stack, "i" |); M.get_name (| globals, locals_stack, "tx" |) ],
        M.call (|
      M.get_name (| globals, locals_stack, "enumerate" |),
      make_list [
        M.call (|
          M.get_name (| globals, locals_stack, "map" |),
          make_list [
            M.get_name (| globals, locals_stack, "decode_transaction" |);
            M.get_name (| globals, locals_stack, "transactions" |)
          ],
          make_dict []
        |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "trie_set" |),
    make_list [
      M.get_name (| globals, locals_stack, "transactions_trie" |);
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_name (| globals, locals_stack, "i" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |);
      M.call (|
        M.get_name (| globals, locals_stack, "encode_transaction" |),
        make_list [
          M.get_name (| globals, locals_stack, "tx" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, locals_stack, "sender_address" |); M.get_name (| globals, locals_stack, "effective_gas_price" |) ],
            M.call (|
              M.get_name (| globals, locals_stack, "check_transaction" |),
              make_list [
                M.get_name (| globals, locals_stack, "tx" |);
                M.get_name (| globals, locals_stack, "base_fee_per_gas" |);
                M.get_name (| globals, locals_stack, "gas_available" |);
                M.get_name (| globals, locals_stack, "chain_id" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "env" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "vm" |), "Environment" |),
              make_list [],
              make_dict []
            |)
          |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, locals_stack, "gas_used" |); M.get_name (| globals, locals_stack, "logs" |); M.get_name (| globals, locals_stack, "error" |) ],
            M.call (|
              M.get_name (| globals, locals_stack, "process_transaction" |),
              make_list [
                M.get_name (| globals, locals_stack, "env" |);
                M.get_name (| globals, locals_stack, "tx" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_op_local (|
            BinOp.sub,
            "gas_available",
            M.get_name (| globals, locals_stack, "gas_used" |)
          |) in
          let _ := M.assign_local (|
            "receipt" ,
            M.call (|
              M.get_name (| globals, locals_stack, "make_receipt" |),
              make_list [
                M.get_name (| globals, locals_stack, "tx" |);
                M.get_name (| globals, locals_stack, "error" |);
                BinOp.sub (|
                  M.get_name (| globals, locals_stack, "block_gas_limit" |),
                  M.get_name (| globals, locals_stack, "gas_available" |)
                |);
                M.get_name (| globals, locals_stack, "logs" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "trie_set" |),
    make_list [
      M.get_name (| globals, locals_stack, "receipts_trie" |);
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "Uint" |),
            make_list [
              M.get_name (| globals, locals_stack, "i" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |);
      M.get_name (| globals, locals_stack, "receipt" |)
    ],
    make_dict []
  |) in
          let _ := M.assign_op_local (|
            BinOp.add,
            "block_logs",
            M.get_name (| globals, locals_stack, "logs" |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "pay_rewards" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "block_number" |);
      M.get_name (| globals, locals_stack, "coinbase" |);
      M.get_name (| globals, locals_stack, "ommers" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "block_gas_used" ,
      BinOp.sub (|
        M.get_name (| globals, locals_stack, "block_gas_limit" |),
        M.get_name (| globals, locals_stack, "gas_available" |)
      |)
    |) in
    let _ := M.assign_local (|
      "block_logs_bloom" ,
      M.call (|
        M.get_name (| globals, locals_stack, "logs_bloom" |),
        make_list [
          M.get_name (| globals, locals_stack, "block_logs" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "ApplyBodyOutput" |),
        make_list [
          M.get_name (| globals, locals_stack, "block_gas_used" |);
          M.call (|
            M.get_name (| globals, locals_stack, "root" |),
            make_list [
              M.get_name (| globals, locals_stack, "transactions_trie" |)
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, locals_stack, "root" |),
            make_list [
              M.get_name (| globals, locals_stack, "receipts_trie" |)
            ],
            make_dict []
          |);
          M.get_name (| globals, locals_stack, "block_logs_bloom" |);
          M.call (|
            M.get_name (| globals, locals_stack, "state_root" |),
            make_list [
              M.get_name (| globals, locals_stack, "state" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom apply_body_in_globals :
  IsInGlobals globals "apply_body" (make_function apply_body).

Definition validate_ommers : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "ommers"; "block_header"; "chain" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Validates the ommers mentioned in the block.

    An ommer block is a block that wasn't canonically added to the
    blockchain because it wasn't validated as fast as the canonical block
    but was mined at the same time.

    To be considered valid, the ommers must adhere to the rules defined in
    the Ethereum protocol. The maximum amount of ommers is 2 per block and
    there cannot be duplicate ommers in a block. Many of the other ommer
    constraints are listed in the in-line comments of this function.

    Parameters
    ----------
    ommers :
        List of ommers mentioned in the current block.
    block_header:
        The header of current block.
    chain :
        History and current state.
    " in
    let _ := M.assign_local (|
      "block_hash" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "rlp_hash" |),
        make_list [
          M.get_name (| globals, locals_stack, "block_header" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "rlp_hash" |),
            make_list [
              M.get_name (| globals, locals_stack, "ommers" |)
            ],
            make_dict []
          |),
          M.get_field (| M.get_name (| globals, locals_stack, "block_header" |), "ommers_hash" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "ommers" |)
            ],
            make_dict []
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.None_
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "ommer" |),
        M.get_name (| globals, locals_stack, "ommers" |),
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.gt (|
                  Constant.int 1,
                  M.get_field (| M.get_name (| globals, locals_stack, "ommer" |), "number" |)
                |),
                ltac:(M.monadic (
                  Compare.gt_e (|
                    M.get_field (| M.get_name (| globals, locals_stack, "ommer" |), "number" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "block_header" |), "number" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_local (|
            "ommer_parent_header" ,
            M.get_field (| M.get_subscript (|
              M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |),
              BinOp.sub (|
                UnOp.sub (| BinOp.sub (|
                  M.get_field (| M.get_name (| globals, locals_stack, "block_header" |), "number" |),
                  M.get_field (| M.get_name (| globals, locals_stack, "ommer" |), "number" |)
                |) |),
                Constant.int 1
              |)
            |), "header" |)
          |) in
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "validate_header" |),
    make_list [
      M.get_name (| globals, locals_stack, "ommer" |);
      M.get_name (| globals, locals_stack, "ommer_parent_header" |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "ommers" |)
            ],
            make_dict []
          |),
          Constant.int 2
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "ommers_hashes" ,
      Constant.str "(* At expr: unsupported node type: ListComp *)"
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "ommers_hashes" |)
            ],
            make_dict []
          |),
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "set" |),
                make_list [
                  M.get_name (| globals, locals_stack, "ommers_hashes" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "recent_canonical_blocks" ,
      M.slice (|
        M.get_field (| M.get_name (| globals, locals_stack, "chain" |), "blocks" |),
        UnOp.sub (| BinOp.add (|
          M.get_name (| globals, locals_stack, "MAX_OMMER_DEPTH" |),
          Constant.int 1
        |) |),
        Constant.None_,
        Constant.None_
      |)
    |) in
    let _ := M.assign_local (|
      "recent_canonical_block_hashes" ,
      Constant.str "(* At expr: unsupported node type: SetComp *)"
    |) in
(* At stmt: unsupported node type: AnnAssign *)
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "block" |),
        M.get_name (| globals, locals_stack, "recent_canonical_blocks" |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "recent_ommers_hashes" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "recent_ommers_hashes" |), "union" |),
              make_list [
                Constant.str "(* At expr: unsupported node type: SetComp *)"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ :=
      M.for_ (|
        make_tuple [ M.get_name (| globals, locals_stack, "ommer_index" |); M.get_name (| globals, locals_stack, "ommer" |) ],
        M.call (|
      M.get_name (| globals, locals_stack, "enumerate" |),
      make_list [
        M.get_name (| globals, locals_stack, "ommers" |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "ommer_hash" ,
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "ommers_hashes" |),
              M.get_name (| globals, locals_stack, "ommer_index" |)
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.eq (|
                M.get_name (| globals, locals_stack, "ommer_hash" |),
                M.get_name (| globals, locals_stack, "block_hash" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.in_ (|
                M.get_name (| globals, locals_stack, "ommer_hash" |),
                M.get_name (| globals, locals_stack, "recent_canonical_block_hashes" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.in_ (|
                M.get_name (| globals, locals_stack, "ommer_hash" |),
                M.get_name (| globals, locals_stack, "recent_ommers_hashes" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_local (|
            "ommer_age" ,
            BinOp.sub (|
              M.get_field (| M.get_name (| globals, locals_stack, "block_header" |), "number" |),
              M.get_field (| M.get_name (| globals, locals_stack, "ommer" |), "number" |)
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.gt (|
                  Constant.int 1,
                  M.get_name (| globals, locals_stack, "ommer_age" |)
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "ommer_age" |),
                    M.get_name (| globals, locals_stack, "MAX_OMMER_DEPTH" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.not_in (|
                M.get_field (| M.get_name (| globals, locals_stack, "ommer" |), "parent_hash" |),
                M.get_name (| globals, locals_stack, "recent_canonical_block_hashes" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.eq (|
                M.get_field (| M.get_name (| globals, locals_stack, "ommer" |), "parent_hash" |),
                M.get_field (| M.get_name (| globals, locals_stack, "block_header" |), "parent_hash" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    M.pure Constant.None_)).

Axiom validate_ommers_in_globals :
  IsInGlobals globals "validate_ommers" (make_function validate_ommers).

Definition pay_rewards : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "state"; "block_number"; "coinbase"; "ommers" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Pay rewards to the block miner as well as the ommers miners.

    The miner of the canonical block is rewarded with the predetermined
    block reward, ``BLOCK_REWARD``, plus a variable award based off of the
    number of ommer blocks that were mined around the same time, and included
    in the canonical block's header. An ommer block is a block that wasn't
    added to the canonical blockchain because it wasn't validated as fast as
    the accepted block but was mined at the same time. Although not all blocks
    that are mined are added to the canonical chain, miners are still paid a
    reward for their efforts. This reward is called an ommer reward and is
    calculated based on the number associated with the ommer block that they
    mined.

    Parameters
    ----------
    state :
        Current account state.
    block_number :
        Position of the block within the chain.
    coinbase :
        Address of account which receives block reward and transaction fees.
    ommers :
        List of ommers mentioned in the current block.
    " in
    let _ := M.assign_local (|
      "miner_reward" ,
      BinOp.add (|
        M.get_name (| globals, locals_stack, "BLOCK_REWARD" |),
        BinOp.mult (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "ommers" |)
            ],
            make_dict []
          |),
          BinOp.floor_div (|
            M.get_name (| globals, locals_stack, "BLOCK_REWARD" |),
            Constant.int 32
          |)
        |)
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "create_ether" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_name (| globals, locals_stack, "coinbase" |);
      M.get_name (| globals, locals_stack, "miner_reward" |)
    ],
    make_dict []
  |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "ommer" |),
        M.get_name (| globals, locals_stack, "ommers" |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "ommer_age" ,
            M.call (|
              M.get_name (| globals, locals_stack, "U256" |),
              make_list [
                BinOp.sub (|
                  M.get_name (| globals, locals_stack, "block_number" |),
                  M.get_field (| M.get_name (| globals, locals_stack, "ommer" |), "number" |)
                |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "ommer_miner_reward" ,
            BinOp.floor_div (|
              BinOp.mult (|
                BinOp.sub (|
                  Constant.int 8,
                  M.get_name (| globals, locals_stack, "ommer_age" |)
                |),
                M.get_name (| globals, locals_stack, "BLOCK_REWARD" |)
              |),
              Constant.int 8
            |)
          |) in
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "create_ether" |),
    make_list [
      M.get_name (| globals, locals_stack, "state" |);
      M.get_field (| M.get_name (| globals, locals_stack, "ommer" |), "coinbase" |);
      M.get_name (| globals, locals_stack, "ommer_miner_reward" |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    M.pure Constant.None_)).

Axiom pay_rewards_in_globals :
  IsInGlobals globals "pay_rewards" (make_function pay_rewards).

Definition process_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "env"; "tx" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Execute a transaction against the provided environment.

    This function processes the actions needed to execute a transaction.
    It decrements the sender's account after calculating the gas fee and
    refunds them the proper amount after execution. Calling contracts,
    deploying code, and incrementing nonces are all examples of actions that
    happen within this function or from a call made within this function.

    Accounts that are marked for deletion are processed and destroyed after
    execution.

    Parameters
    ----------
    env :
        Environment for the Ethereum Virtual Machine.
    tx :
        Transaction to execute.

    Returns
    -------
    gas_left : `ethereum.base_types.U256`
        Remaining gas after execution.
    logs : `Tuple[ethereum.blocks.Log, ...]`
        Logs generated during execution.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        UnOp.not (| M.call (|
          M.get_name (| globals, locals_stack, "validate_transaction" |),
          make_list [
            M.get_name (| globals, locals_stack, "tx" |)
          ],
          make_dict []
        |) |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "sender" ,
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "origin" |)
    |) in
    let _ := M.assign_local (|
      "sender_account" ,
      M.call (|
        M.get_name (| globals, locals_stack, "get_account" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
          M.get_name (| globals, locals_stack, "sender" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "tx" |);
            M.get_name (| globals, locals_stack, "FeeMarketTransaction" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "max_gas_fee" ,
          BinOp.mult (|
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |),
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "max_fee_per_gas" |)
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "max_gas_fee" ,
          BinOp.mult (|
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |),
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas_price" |)
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "sender_account" |), "nonce" |),
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "nonce" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_field (| M.get_name (| globals, locals_stack, "sender_account" |), "balance" |),
          BinOp.add (|
            M.get_name (| globals, locals_stack, "max_gas_fee" |),
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "value" |)
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "sender_account" |), "code" |),
          M.call (|
            M.get_name (| globals, locals_stack, "bytearray" |),
            make_list [],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "effective_gas_fee" ,
      BinOp.mult (|
        M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |),
        M.get_field (| M.get_name (| globals, locals_stack, "env" |), "gas_price" |)
      |)
    |) in
    let _ := M.assign_local (|
      "gas" ,
      BinOp.sub (|
        M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |),
        M.call (|
          M.get_name (| globals, locals_stack, "calculate_intrinsic_cost" |),
          make_list [
            M.get_name (| globals, locals_stack, "tx" |)
          ],
          make_dict []
        |)
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_name (| globals, locals_stack, "sender" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "sender_balance_after_gas_fee" ,
      BinOp.sub (|
        M.get_field (| M.get_name (| globals, locals_stack, "sender_account" |), "balance" |),
        M.get_name (| globals, locals_stack, "effective_gas_fee" |)
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_name (| globals, locals_stack, "sender" |);
      M.get_name (| globals, locals_stack, "sender_balance_after_gas_fee" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "preaccessed_addresses" ,
      M.call (|
        M.get_name (| globals, locals_stack, "set" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "preaccessed_storage_keys" ,
      M.call (|
        M.get_name (| globals, locals_stack, "set" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "tx" |);
            make_tuple [ M.get_name (| globals, locals_stack, "AccessListTransaction" |); M.get_name (| globals, locals_stack, "FeeMarketTransaction" |) ]
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          M.for_ (|
            make_tuple [ M.get_name (| globals, locals_stack, "address" |); M.get_name (| globals, locals_stack, "keys" |) ],
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "access_list" |),
            ltac:(M.monadic (
              let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "preaccessed_addresses" |), "add" |),
    make_list [
      M.get_name (| globals, locals_stack, "address" |)
    ],
    make_dict []
  |) in
              let _ :=
                M.for_ (|
                  M.get_name (| globals, locals_stack, "key" |),
                  M.get_name (| globals, locals_stack, "keys" |),
                  ltac:(M.monadic (
                    let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "preaccessed_storage_keys" |), "add" |),
    make_list [
      make_tuple [ M.get_name (| globals, locals_stack, "address" |); M.get_name (| globals, locals_stack, "key" |) ]
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
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "message" ,
      M.call (|
        M.get_name (| globals, locals_stack, "prepare_message" |),
        make_list [
          M.get_name (| globals, locals_stack, "sender" |);
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "to" |);
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "value" |);
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "data" |);
          M.get_name (| globals, locals_stack, "gas" |);
          M.get_name (| globals, locals_stack, "env" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "output" ,
      M.call (|
        M.get_name (| globals, locals_stack, "process_message_call" |),
        make_list [
          M.get_name (| globals, locals_stack, "message" |);
          M.get_name (| globals, locals_stack, "env" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "gas_used" ,
      BinOp.sub (|
        M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |),
        M.get_field (| M.get_name (| globals, locals_stack, "output" |), "gas_left" |)
      |)
    |) in
    let _ := M.assign_local (|
      "gas_refund" ,
      M.call (|
        M.get_name (| globals, locals_stack, "min" |),
        make_list [
          BinOp.floor_div (|
            M.get_name (| globals, locals_stack, "gas_used" |),
            Constant.int 5
          |);
          M.get_field (| M.get_name (| globals, locals_stack, "output" |), "refund_counter" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "gas_refund_amount" ,
      BinOp.mult (|
        BinOp.add (|
          M.get_field (| M.get_name (| globals, locals_stack, "output" |), "gas_left" |),
          M.get_name (| globals, locals_stack, "gas_refund" |)
        |),
        M.get_field (| M.get_name (| globals, locals_stack, "env" |), "gas_price" |)
      |)
    |) in
    let _ := M.assign_local (|
      "priority_fee_per_gas" ,
      BinOp.sub (|
        M.get_field (| M.get_name (| globals, locals_stack, "env" |), "gas_price" |),
        M.get_field (| M.get_name (| globals, locals_stack, "env" |), "base_fee_per_gas" |)
      |)
    |) in
    let _ := M.assign_local (|
      "transaction_fee" ,
      BinOp.mult (|
        BinOp.sub (|
          BinOp.sub (|
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |),
            M.get_field (| M.get_name (| globals, locals_stack, "output" |), "gas_left" |)
          |),
          M.get_name (| globals, locals_stack, "gas_refund" |)
        |),
        M.get_name (| globals, locals_stack, "priority_fee_per_gas" |)
      |)
    |) in
    let _ := M.assign_local (|
      "total_gas_used" ,
      BinOp.sub (|
        M.get_name (| globals, locals_stack, "gas_used" |),
        M.get_name (| globals, locals_stack, "gas_refund" |)
      |)
    |) in
    let _ := M.assign_local (|
      "sender_balance_after_refund" ,
      BinOp.add (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "get_account" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
            M.get_name (| globals, locals_stack, "sender" |)
          ],
          make_dict []
        |), "balance" |),
        M.get_name (| globals, locals_stack, "gas_refund_amount" |)
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_name (| globals, locals_stack, "sender" |);
      M.get_name (| globals, locals_stack, "sender_balance_after_refund" |)
    ],
    make_dict []
  |) in
    let _ := M.assign_local (|
      "coinbase_balance_after_mining_fee" ,
      BinOp.add (|
        M.get_field (| M.call (|
          M.get_name (| globals, locals_stack, "get_account" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
            M.get_field (| M.get_name (| globals, locals_stack, "env" |), "coinbase" |)
          ],
          make_dict []
        |), "balance" |),
        M.get_name (| globals, locals_stack, "transaction_fee" |)
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_name (| globals, locals_stack, "coinbase_balance_after_mining_fee" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, locals_stack, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "coinbase" |);
      M.get_name (| globals, locals_stack, "coinbase_balance_after_mining_fee" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, locals_stack, "account_exists_and_is_empty" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
                M.get_field (| M.get_name (| globals, locals_stack, "env" |), "coinbase" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.call (|
    M.get_name (| globals, locals_stack, "destroy_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "coinbase" |)
    ],
    make_dict []
  |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "address" |),
        M.get_field (| M.get_name (| globals, locals_stack, "output" |), "accounts_to_delete" |),
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "destroy_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_name (| globals, locals_stack, "address" |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "address" |),
        M.get_field (| M.get_name (| globals, locals_stack, "output" |), "touched_accounts" |),
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              M.call (|
                M.get_name (| globals, locals_stack, "account_exists_and_is_empty" |),
                make_list [
                  M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
                  M.get_name (| globals, locals_stack, "address" |)
                ],
                make_dict []
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.call (|
    M.get_name (| globals, locals_stack, "destroy_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, locals_stack, "env" |), "state" |);
      M.get_name (| globals, locals_stack, "address" |)
    ],
    make_dict []
  |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      make_tuple [ M.get_name (| globals, locals_stack, "total_gas_used" |); M.get_field (| M.get_name (| globals, locals_stack, "output" |), "logs" |); M.get_field (| M.get_name (| globals, locals_stack, "output" |), "error" |) ]
    |) in
    M.pure Constant.None_)).

Axiom process_transaction_in_globals :
  IsInGlobals globals "process_transaction" (make_function process_transaction).

Definition validate_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "tx" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Verifies a transaction.

    The gas in a transaction gets used to pay for the intrinsic cost of
    operations, therefore if there is insufficient gas then it would not
    be possible to execute a transaction and it will be declared invalid.

    Additionally, the nonce of a transaction must not equal or exceed the
    limit defined in `EIP-2681 <https://eips.ethereum.org/EIPS/eip-2681>`_.
    In practice, defining the limit as ``2**64-1`` has no impact because
    sending ``2**64-1`` transactions is improbable. It's not strictly
    impossible though, ``2**64-1`` transactions is the entire capacity of the
    Ethereum blockchain at 2022 gas limits for a little over 22 years.

    Parameters
    ----------
    tx :
        Transaction to validate.

    Returns
    -------
    verified : `bool`
        True if the transaction can be executed, or False otherwise.
    " in
    let _ := M.return_ (|
      BoolOp.and (|
        Compare.lt_e (|
          M.call (|
            M.get_name (| globals, locals_stack, "calculate_intrinsic_cost" |),
            make_list [
              M.get_name (| globals, locals_stack, "tx" |)
            ],
            make_dict []
          |),
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |)
        |),
        ltac:(M.monadic (
          Compare.lt (|
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "nonce" |),
            BinOp.sub (|
              BinOp.pow (|
                Constant.int 2,
                Constant.int 64
              |),
              Constant.int 1
            |)
          |)
        ))
      |)
    |) in
    M.pure Constant.None_)).

Axiom validate_transaction_in_globals :
  IsInGlobals globals "validate_transaction" (make_function validate_transaction).

Definition calculate_intrinsic_cost : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "tx" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Calculates the gas that is charged before execution is started.

    The intrinsic cost of the transaction is charged before execution has
    begun. Functions/operations in the EVM cost money to execute so this
    intrinsic cost is for the operations that need to be paid for as part of
    the transaction. Data transfer, for example, is part of this intrinsic
    cost. It costs ether to send data over the wire and that ether is
    accounted for in the intrinsic cost calculated in this function. This
    intrinsic cost must be calculated and paid for before execution in order
    for all operations to be implemented.

    Parameters
    ----------
    tx :
        Transaction to compute the intrinsic cost of.

    Returns
    -------
    verified : `ethereum.base_types.Uint`
        The intrinsic cost of the transaction.
    " in
    let _ := M.assign_local (|
      "data_cost" ,
      Constant.int 0
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "byte" |),
        M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "data" |),
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.eq (|
                M.get_name (| globals, locals_stack, "byte" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.assign_op_local (|
                BinOp.add,
                "data_cost",
                M.get_name (| globals, locals_stack, "TX_DATA_COST_PER_ZERO" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              let _ := M.assign_op_local (|
                BinOp.add,
                "data_cost",
                M.get_name (| globals, locals_stack, "TX_DATA_COST_PER_NON_ZERO" |)
              |) in
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "to" |),
          M.call (|
            M.get_name (| globals, locals_stack, "Bytes0" |),
            make_list [
              Constant.bytes ""
            ],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "create_cost" ,
          M.get_name (| globals, locals_stack, "TX_CREATE_COST" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign_local (|
          "create_cost" ,
          Constant.int 0
        |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "access_list_cost" ,
      Constant.int 0
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "tx" |);
            make_tuple [ M.get_name (| globals, locals_stack, "AccessListTransaction" |); M.get_name (| globals, locals_stack, "FeeMarketTransaction" |) ]
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          M.for_ (|
            make_tuple [ M.get_name (| globals, locals_stack, "_address" |); M.get_name (| globals, locals_stack, "keys" |) ],
            M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "access_list" |),
            ltac:(M.monadic (
              let _ := M.assign_op_local (|
                BinOp.add,
                "access_list_cost",
                M.get_name (| globals, locals_stack, "TX_ACCESS_LIST_ADDRESS_COST" |)
              |) in
              let _ := M.assign_op_local (|
                BinOp.add,
                "access_list_cost",
                BinOp.mult (|
    M.call (|
      M.get_name (| globals, locals_stack, "len" |),
      make_list [
        M.get_name (| globals, locals_stack, "keys" |)
      ],
      make_dict []
    |),
    M.get_name (| globals, locals_stack, "TX_ACCESS_LIST_STORAGE_KEY_COST" |)
  |)
              |) in
              M.pure Constant.None_
            )),
            ltac:(M.monadic (
              M.pure Constant.None_
            ))
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          BinOp.add (|
            BinOp.add (|
              BinOp.add (|
                M.get_name (| globals, locals_stack, "TX_BASE_COST" |),
                M.get_name (| globals, locals_stack, "data_cost" |)
              |),
              M.get_name (| globals, locals_stack, "create_cost" |)
            |),
            M.get_name (| globals, locals_stack, "access_list_cost" |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom calculate_intrinsic_cost_in_globals :
  IsInGlobals globals "calculate_intrinsic_cost" (make_function calculate_intrinsic_cost).

Definition recover_sender : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "chain_id"; "tx" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Extracts the sender address from a transaction.

    The v, r, and s values are the three parts that make up the signature
    of a transaction. In order to recover the sender of a transaction the two
    components needed are the signature (``v``, ``r``, and ``s``) and the
    signing hash of the transaction. The sender's public key can be obtained
    with these two values and therefore the sender address can be retrieved.

    Parameters
    ----------
    tx :
        Transaction of interest.
    chain_id :
        ID of the executing chain.

    Returns
    -------
    sender : `ethereum.fork_types.Address`
        The address of the account that signed the transaction.
    " in
    let _ := M.assign (|
      make_tuple [ M.get_name (| globals, locals_stack, "r" |); M.get_name (| globals, locals_stack, "s" |) ],
      make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "r" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "s" |) ]
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.gt_e (|
            Constant.int 0,
            M.get_name (| globals, locals_stack, "r" |)
          |),
          ltac:(M.monadic (
            Compare.gt_e (|
              M.get_name (| globals, locals_stack, "r" |),
              M.get_name (| globals, locals_stack, "SECP256K1N" |)
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.gt_e (|
            Constant.int 0,
            M.get_name (| globals, locals_stack, "s" |)
          |),
          ltac:(M.monadic (
            Compare.gt (|
              M.get_name (| globals, locals_stack, "s" |),
              BinOp.floor_div (|
                M.get_name (| globals, locals_stack, "SECP256K1N" |),
                Constant.int 2
              |)
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "tx" |);
            M.get_name (| globals, locals_stack, "LegacyTransaction" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "v" ,
          M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "v" |)
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
              Compare.eq (|
                M.get_name (| globals, locals_stack, "v" |),
                Constant.int 27
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_name (| globals, locals_stack, "v" |),
                  Constant.int 28
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "public_key" ,
              M.call (|
                M.get_name (| globals, locals_stack, "secp256k1_recover" |),
                make_list [
                  M.get_name (| globals, locals_stack, "r" |);
                  M.get_name (| globals, locals_stack, "s" |);
                  BinOp.sub (|
                    M.get_name (| globals, locals_stack, "v" |),
                    Constant.int 27
                  |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "signing_hash_pre155" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "tx" |)
                    ],
                    make_dict []
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
                BoolOp.and (|
                  Compare.not_eq (|
                    M.get_name (| globals, locals_stack, "v" |),
                    BinOp.add (|
                      Constant.int 35,
                      BinOp.mult (|
                        M.get_name (| globals, locals_stack, "chain_id" |),
                        Constant.int 2
                      |)
                    |)
                  |),
                  ltac:(M.monadic (
                    Compare.not_eq (|
                      M.get_name (| globals, locals_stack, "v" |),
                      BinOp.add (|
                        Constant.int 36,
                        BinOp.mult (|
                          M.get_name (| globals, locals_stack, "chain_id" |),
                          Constant.int 2
                        |)
                      |)
                    |)
                  ))
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "InvalidBlock" |)) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ := M.assign_local (|
              "public_key" ,
              M.call (|
                M.get_name (| globals, locals_stack, "secp256k1_recover" |),
                make_list [
                  M.get_name (| globals, locals_stack, "r" |);
                  M.get_name (| globals, locals_stack, "s" |);
                  BinOp.sub (|
                    BinOp.sub (|
                      M.get_name (| globals, locals_stack, "v" |),
                      Constant.int 35
                    |),
                    BinOp.mult (|
                      M.get_name (| globals, locals_stack, "chain_id" |),
                      Constant.int 2
                    |)
                  |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "signing_hash_155" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "tx" |);
                      M.get_name (| globals, locals_stack, "chain_id" |)
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            M.call (|
              M.get_name (| globals, locals_stack, "isinstance" |),
              make_list [
                M.get_name (| globals, locals_stack, "tx" |);
                M.get_name (| globals, locals_stack, "AccessListTransaction" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "public_key" ,
              M.call (|
                M.get_name (| globals, locals_stack, "secp256k1_recover" |),
                make_list [
                  M.get_name (| globals, locals_stack, "r" |);
                  M.get_name (| globals, locals_stack, "s" |);
                  M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "y_parity" |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "signing_hash_2930" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "tx" |)
                    ],
                    make_dict []
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
                M.call (|
                  M.get_name (| globals, locals_stack, "isinstance" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "tx" |);
                    M.get_name (| globals, locals_stack, "FeeMarketTransaction" |)
                  ],
                  make_dict []
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.assign_local (|
                  "public_key" ,
                  M.call (|
                    M.get_name (| globals, locals_stack, "secp256k1_recover" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "r" |);
                      M.get_name (| globals, locals_stack, "s" |);
                      M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "y_parity" |);
                      M.call (|
                        M.get_name (| globals, locals_stack, "signing_hash_1559" |),
                        make_list [
                          M.get_name (| globals, locals_stack, "tx" |)
                        ],
                        make_dict []
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
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Address" |),
        make_list [
          M.slice (|
            M.call (|
              M.get_name (| globals, locals_stack, "keccak256" |),
              make_list [
                M.get_name (| globals, locals_stack, "public_key" |)
              ],
              make_dict []
            |),
            Constant.int 12,
            Constant.int 32,
            Constant.None_
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom recover_sender_in_globals :
  IsInGlobals globals "recover_sender" (make_function recover_sender).

Definition signing_hash_pre155 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "tx" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Compute the hash of a transaction used in a legacy (pre EIP 155) signature.

    Parameters
    ----------
    tx :
        Transaction of interest.

    Returns
    -------
    hash : `ethereum.crypto.hash.Hash32`
        Hash of the transaction.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
            make_list [
              make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "nonce" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas_price" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "to" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "value" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "data" |) ]
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom signing_hash_pre155_in_globals :
  IsInGlobals globals "signing_hash_pre155" (make_function signing_hash_pre155).

Definition signing_hash_155 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "tx"; "chain_id" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Compute the hash of a transaction used in a EIP 155 signature.

    Parameters
    ----------
    tx :
        Transaction of interest.
    chain_id :
        The id of the current chain.

    Returns
    -------
    hash : `ethereum.crypto.hash.Hash32`
        Hash of the transaction.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
            make_list [
              make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "nonce" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas_price" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "to" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "value" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "data" |); M.get_name (| globals, locals_stack, "chain_id" |); M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |); M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |) ]
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom signing_hash_155_in_globals :
  IsInGlobals globals "signing_hash_155" (make_function signing_hash_155).

Definition signing_hash_2930 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "tx" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Compute the hash of a transaction used in a EIP 2930 signature.

    Parameters
    ----------
    tx :
        Transaction of interest.

    Returns
    -------
    hash : `ethereum.crypto.hash.Hash32`
        Hash of the transaction.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          BinOp.add (|
            Constant.bytes "01",
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
              make_list [
                make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "chain_id" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "nonce" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas_price" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "to" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "value" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "data" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "access_list" |) ]
              ],
              make_dict []
            |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom signing_hash_2930_in_globals :
  IsInGlobals globals "signing_hash_2930" (make_function signing_hash_2930).

Definition signing_hash_1559 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "tx" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Compute the hash of a transaction used in a EIP 1559 signature.

    Parameters
    ----------
    tx :
        Transaction of interest.

    Returns
    -------
    hash : `ethereum.crypto.hash.Hash32`
        Hash of the transaction.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          BinOp.add (|
            Constant.bytes "02",
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
              make_list [
                make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "chain_id" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "nonce" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "max_priority_fee_per_gas" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "max_fee_per_gas" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "gas" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "to" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "value" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "data" |); M.get_field (| M.get_name (| globals, locals_stack, "tx" |), "access_list" |) ]
              ],
              make_dict []
            |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom signing_hash_1559_in_globals :
  IsInGlobals globals "signing_hash_1559" (make_function signing_hash_1559).

Definition compute_header_hash : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "header" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Computes the hash of a block header.

    The header hash of a block is the canonical hash that is used to refer
    to a specific block and completely distinguishes a block from another.

    ``keccak256`` is a function that produces a 256 bit hash of any input.
    It also takes in any number of bytes as an input and produces a single
    hash for them. A hash is a completely unique output for a single input.
    So an input corresponds to one unique hash that can be used to identify
    the input exactly.

    Prior to using the ``keccak256`` hash function, the header must be
    encoded using the Recursive-Length Prefix. See :ref:`rlp`.
    RLP encoding the header converts it into a space-efficient format that
    allows for easy transfer of data between nodes. The purpose of RLP is to
    encode arbitrarily nested arrays of binary data, and RLP is the primary
    encoding method used to serialize objects in Ethereum's execution layer.
    The only purpose of RLP is to encode structure; encoding specific data
    types (e.g. strings, floats) is left up to higher-order protocols.

    Parameters
    ----------
    header :
        Header of interest.

    Returns
    -------
    hash : `ethereum.crypto.hash.Hash32`
        Hash of the header.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
            make_list [
              M.get_name (| globals, locals_stack, "header" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom compute_header_hash_in_globals :
  IsInGlobals globals "compute_header_hash" (make_function compute_header_hash).

Definition check_gas_limit : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "gas_limit"; "parent_gas_limit" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Validates the gas limit for a block.

    The bounds of the gas limit, ``max_adjustment_delta``, is set as the
    quotient of the parent block's gas limit and the
    ``GAS_LIMIT_ADJUSTMENT_FACTOR``. Therefore, if the gas limit that is
    passed through as a parameter is greater than or equal to the *sum* of
    the parent's gas and the adjustment delta then the limit for gas is too
    high and fails this function's check. Similarly, if the limit is less
    than or equal to the *difference* of the parent's gas and the adjustment
    delta *or* the predefined ``GAS_LIMIT_MINIMUM`` then this function's
    check fails because the gas limit doesn't allow for a sufficient or
    reasonable amount of gas to be used on a block.

    Parameters
    ----------
    gas_limit :
        Gas limit to validate.

    parent_gas_limit :
        Gas limit of the parent block.

    Returns
    -------
    check : `bool`
        True if gas limit constraints are satisfied, False otherwise.
    " in
    let _ := M.assign_local (|
      "max_adjustment_delta" ,
      BinOp.floor_div (|
        M.get_name (| globals, locals_stack, "parent_gas_limit" |),
        M.get_name (| globals, locals_stack, "GAS_LIMIT_ADJUSTMENT_FACTOR" |)
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt_e (|
          M.get_name (| globals, locals_stack, "gas_limit" |),
          BinOp.add (|
            M.get_name (| globals, locals_stack, "parent_gas_limit" |),
            M.get_name (| globals, locals_stack, "max_adjustment_delta" |)
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.bool false
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt_e (|
          M.get_name (| globals, locals_stack, "gas_limit" |),
          BinOp.sub (|
            M.get_name (| globals, locals_stack, "parent_gas_limit" |),
            M.get_name (| globals, locals_stack, "max_adjustment_delta" |)
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.bool false
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.get_name (| globals, locals_stack, "gas_limit" |),
          M.get_name (| globals, locals_stack, "GAS_LIMIT_MINIMUM" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          Constant.bool false
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      Constant.bool true
    |) in
    M.pure Constant.None_)).

Axiom check_gas_limit_in_globals :
  IsInGlobals globals "check_gas_limit" (make_function check_gas_limit).

Definition calculate_block_difficulty : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "block_number"; "block_timestamp"; "parent_timestamp"; "parent_difficulty"; "parent_has_ommers" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Computes difficulty of a block using its header and parent header.

    The difficulty is determined by the time the block was created after its
    parent. The ``offset`` is calculated using the parent block's difficulty,
    ``parent_difficulty``, and the timestamp between blocks. This offset is
    then added to the parent difficulty and is stored as the ``difficulty``
    variable. If the time between the block and its parent is too short, the
    offset will result in a positive number thus making the sum of
    ``parent_difficulty`` and ``offset`` to be a greater value in order to
    avoid mass forking. But, if the time is long enough, then the offset
    results in a negative value making the block less difficult than
    its parent.

    The base standard for a block's difficulty is the predefined value
    set for the genesis block since it has no parent. So, a block
    can't be less difficult than the genesis block, therefore each block's
    difficulty is set to the maximum value between the calculated
    difficulty and the ``GENESIS_DIFFICULTY``.

    Parameters
    ----------
    block_number :
        Block number of the block.
    block_timestamp :
        Timestamp of the block.
    parent_timestamp :
        Timestamp of the parent block.
    parent_difficulty :
        difficulty of the parent block.
    parent_has_ommers:
        does the parent have ommers.

    Returns
    -------
    difficulty : `ethereum.base_types.Uint`
        Computed difficulty for a block.
    " in
    let _ := M.assign_local (|
      "offset" ,
      BinOp.mult (|
        BinOp.floor_div (|
          M.call (|
            M.get_name (| globals, locals_stack, "int" |),
            make_list [
              M.get_name (| globals, locals_stack, "parent_difficulty" |)
            ],
            make_dict []
          |),
          Constant.int 2048
        |),
        M.call (|
          M.get_name (| globals, locals_stack, "max" |),
          make_list [
            BinOp.sub (|
                            (* if *)
              M.if_then_else (|
                M.get_name (| globals, locals_stack, "parent_has_ommers" |),
              (* then *)
              ltac:(M.monadic (
Constant.int 2
              (* else *)
              )), ltac:(M.monadic (
Constant.int 1
              )) |),
              BinOp.floor_div (|
                M.call (|
                  M.get_name (| globals, locals_stack, "int" |),
                  make_list [
                    BinOp.sub (|
                      M.get_name (| globals, locals_stack, "block_timestamp" |),
                      M.get_name (| globals, locals_stack, "parent_timestamp" |)
                    |)
                  ],
                  make_dict []
                |),
                Constant.int 9
              |)
            |);
            UnOp.sub (| Constant.int 99 |)
          ],
          make_dict []
        |)
      |)
    |) in
    let _ := M.assign_local (|
      "difficulty" ,
      BinOp.add (|
        M.call (|
          M.get_name (| globals, locals_stack, "int" |),
          make_list [
            M.get_name (| globals, locals_stack, "parent_difficulty" |)
          ],
          make_dict []
        |),
        M.get_name (| globals, locals_stack, "offset" |)
      |)
    |) in
    let _ := M.assign_local (|
      "num_bomb_periods" ,
      BinOp.sub (|
        BinOp.floor_div (|
          BinOp.sub (|
            M.call (|
              M.get_name (| globals, locals_stack, "int" |),
              make_list [
                M.get_name (| globals, locals_stack, "block_number" |)
              ],
              make_dict []
            |),
            M.get_name (| globals, locals_stack, "BOMB_DELAY_BLOCKS" |)
          |),
          Constant.int 100000
        |),
        Constant.int 2
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt_e (|
          M.get_name (| globals, locals_stack, "num_bomb_periods" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_op_local (|
          BinOp.add,
          "difficulty",
          BinOp.pow (|
    Constant.int 2,
    M.get_name (| globals, locals_stack, "num_bomb_periods" |)
  |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "max" |),
            make_list [
              M.get_name (| globals, locals_stack, "difficulty" |);
              M.get_name (| globals, locals_stack, "MINIMUM_DIFFICULTY" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom calculate_block_difficulty_in_globals :
  IsInGlobals globals "calculate_block_difficulty" (make_function calculate_block_difficulty).
