Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require typing.
Axiom typing_List :
  IsGlobalAlias globals typing.globals "List".
Axiom typing_Optional :
  IsGlobalAlias globals typing.globals "Optional".
Axiom typing_Set_ :
  IsGlobalAlias globals typing.globals "Set_".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".

Require ethereum.base_types.
Axiom ethereum_base_types_Bytes0 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes0".

Require ethereum.crypto.elliptic_curve.
Axiom ethereum_crypto_elliptic_curve_SECP256K1N :
  IsGlobalAlias globals ethereum.crypto.elliptic_curve.globals "SECP256K1N".
Axiom ethereum_crypto_elliptic_curve_secp256k1_recover :
  IsGlobalAlias globals ethereum.crypto.elliptic_curve.globals "secp256k1_recover".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_Hash32 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "Hash32".
Axiom ethereum_crypto_hash_keccak256 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak256".

Require ethereum.ethash.
Axiom ethereum_ethash_dataset_size :
  IsGlobalAlias globals ethereum.ethash.globals "dataset_size".
Axiom ethereum_ethash_generate_cache :
  IsGlobalAlias globals ethereum.ethash.globals "generate_cache".
Axiom ethereum_ethash_hashimoto_light :
  IsGlobalAlias globals ethereum.ethash.globals "hashimoto_light".

Require ethereum.exceptions.
Axiom ethereum_exceptions_InvalidBlock :
  IsGlobalAlias globals ethereum.exceptions.globals "InvalidBlock".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require ethereum.__init__.
Axiom ethereum___init___rlp :
  IsGlobalAlias globals ethereum.__init__.globals "rlp".

Require ethereum.base_types.
Axiom ethereum_base_types_U64 :
  IsGlobalAlias globals ethereum.base_types.globals "U64".
Axiom ethereum_base_types_U256 :
  IsGlobalAlias globals ethereum.base_types.globals "U256".
Axiom ethereum_base_types_U256_CEIL_VALUE :
  IsGlobalAlias globals ethereum.base_types.globals "U256_CEIL_VALUE".
Axiom ethereum_base_types_Bytes :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.constantinople.__init__.
Axiom ethereum_constantinople___init___vm :
  IsGlobalAlias globals ethereum.constantinople.__init__.globals "vm".

Require ethereum.constantinople.blocks.
Axiom ethereum_constantinople_blocks_Block :
  IsGlobalAlias globals ethereum.constantinople.blocks.globals "Block".
Axiom ethereum_constantinople_blocks_Header :
  IsGlobalAlias globals ethereum.constantinople.blocks.globals "Header".
Axiom ethereum_constantinople_blocks_Log :
  IsGlobalAlias globals ethereum.constantinople.blocks.globals "Log".
Axiom ethereum_constantinople_blocks_Receipt :
  IsGlobalAlias globals ethereum.constantinople.blocks.globals "Receipt".

Require ethereum.constantinople.bloom.
Axiom ethereum_constantinople_bloom_logs_bloom :
  IsGlobalAlias globals ethereum.constantinople.bloom.globals "logs_bloom".

Require ethereum.constantinople.fork_types.
Axiom ethereum_constantinople_fork_types_Address :
  IsGlobalAlias globals ethereum.constantinople.fork_types.globals "Address".
Axiom ethereum_constantinople_fork_types_Bloom :
  IsGlobalAlias globals ethereum.constantinople.fork_types.globals "Bloom".
Axiom ethereum_constantinople_fork_types_Root :
  IsGlobalAlias globals ethereum.constantinople.fork_types.globals "Root".

Require ethereum.constantinople.state.
Axiom ethereum_constantinople_state_State :
  IsGlobalAlias globals ethereum.constantinople.state.globals "State".
Axiom ethereum_constantinople_state_account_exists_and_is_empty :
  IsGlobalAlias globals ethereum.constantinople.state.globals "account_exists_and_is_empty".
Axiom ethereum_constantinople_state_create_ether :
  IsGlobalAlias globals ethereum.constantinople.state.globals "create_ether".
Axiom ethereum_constantinople_state_destroy_account :
  IsGlobalAlias globals ethereum.constantinople.state.globals "destroy_account".
Axiom ethereum_constantinople_state_get_account :
  IsGlobalAlias globals ethereum.constantinople.state.globals "get_account".
Axiom ethereum_constantinople_state_increment_nonce :
  IsGlobalAlias globals ethereum.constantinople.state.globals "increment_nonce".
Axiom ethereum_constantinople_state_set_account_balance :
  IsGlobalAlias globals ethereum.constantinople.state.globals "set_account_balance".
Axiom ethereum_constantinople_state_state_root :
  IsGlobalAlias globals ethereum.constantinople.state.globals "state_root".

Require ethereum.constantinople.transactions.
Axiom ethereum_constantinople_transactions_TX_BASE_COST :
  IsGlobalAlias globals ethereum.constantinople.transactions.globals "TX_BASE_COST".
Axiom ethereum_constantinople_transactions_TX_CREATE_COST :
  IsGlobalAlias globals ethereum.constantinople.transactions.globals "TX_CREATE_COST".
Axiom ethereum_constantinople_transactions_TX_DATA_COST_PER_NON_ZERO :
  IsGlobalAlias globals ethereum.constantinople.transactions.globals "TX_DATA_COST_PER_NON_ZERO".
Axiom ethereum_constantinople_transactions_TX_DATA_COST_PER_ZERO :
  IsGlobalAlias globals ethereum.constantinople.transactions.globals "TX_DATA_COST_PER_ZERO".
Axiom ethereum_constantinople_transactions_Transaction :
  IsGlobalAlias globals ethereum.constantinople.transactions.globals "Transaction".

Require ethereum.constantinople.trie.
Axiom ethereum_constantinople_trie_Trie :
  IsGlobalAlias globals ethereum.constantinople.trie.globals "Trie".
Axiom ethereum_constantinople_trie_root :
  IsGlobalAlias globals ethereum.constantinople.trie.globals "root".
Axiom ethereum_constantinople_trie_trie_set :
  IsGlobalAlias globals ethereum.constantinople.trie.globals "trie_set".

Require ethereum.constantinople.utils.message.
Axiom ethereum_constantinople_utils_message_prepare_message :
  IsGlobalAlias globals ethereum.constantinople.utils.message.globals "prepare_message".

Require ethereum.constantinople.vm.interpreter.
Axiom ethereum_constantinople_vm_interpreter_process_message_call :
  IsGlobalAlias globals ethereum.constantinople.vm.interpreter.globals "process_message_call".

Definition BLOCK_REWARD : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "U256" |),
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

Definition GAS_LIMIT_ADJUSTMENT_FACTOR : Value.t := M.run ltac:(M.monadic (
  Constant.int 1024
)).

Definition GAS_LIMIT_MINIMUM : Value.t := M.run ltac:(M.monadic (
  Constant.int 5000
)).

Definition MINIMUM_DIFFICULTY : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Uint" |),
    make_list [
      Constant.int 131072
    ],
    make_dict []
  |)
)).

Definition MAX_OMMER_DEPTH : Value.t := M.run ltac:(M.monadic (
  Constant.int 6
)).

Definition BOMB_DELAY_BLOCKS : Value.t := M.run ltac:(M.monadic (
  Constant.int 5000000
)).

Definition EMPTY_OMMER_HASH : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "keccak256" |),
    make_list [
      M.call (|
        M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
        make_list [
          make_list []
        ],
        make_dict []
      |)
    ],
    make_dict []
  |)
)).

Definition BlockChain : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition apply_fork : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "old" ] |) in
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
      M.get_name (| globals, "old" |)
    |) in
    M.pure Constant.None_)).

Definition get_last_256_block_hashes : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "chain" ] |) in
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
    let recent_blocks :=
      M.get_subscript (| M.get_field (| M.get_name (| globals, "chain" |), "blocks" |), M.slice (| UnOp.sub (| Constant.int 255 |), Constant.None_ |) |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "recent_blocks" |)
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
    let recent_block_hashes :=
      make_list [] in
    For M.get_name (| globals, "block" |) in M.get_name (| globals, "recent_blocks" |) do
      let prev_block_hash :=
        M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "parent_hash" |) in
      let _ := M.call (|
    M.get_field (| M.get_name (| globals, "recent_block_hashes" |), "append" |),
    make_list [
      M.get_name (| globals, "prev_block_hash" |)
    ],
    make_dict []
  |) in
    EndFor.
    let most_recent_block_hash :=
      M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
            make_list [
              M.get_field (| M.get_subscript (| M.get_name (| globals, "recent_blocks" |), UnOp.sub (| Constant.int 1 |) |), "header" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_field (| M.get_name (| globals, "recent_block_hashes" |), "append" |),
    make_list [
      M.get_name (| globals, "most_recent_block_hash" |)
    ],
    make_dict []
  |) in
    let _ := M.return_ (|
      M.get_name (| globals, "recent_block_hashes" |)
    |) in
    M.pure Constant.None_)).

Definition state_transition : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "chain"; "block" ] |) in
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
    let parent_header :=
      M.get_field (| M.get_subscript (| M.get_field (| M.get_name (| globals, "chain" |), "blocks" |), UnOp.sub (| Constant.int 1 |) |), "header" |) in
    let _ := M.call (|
    M.get_name (| globals, "validate_header" |),
    make_list [
      M.get_field (| M.get_name (| globals, "block" |), "header" |);
      M.get_name (| globals, "parent_header" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "validate_ommers" |),
    make_list [
      M.get_field (| M.get_name (| globals, "block" |), "ommers" |);
      M.get_field (| M.get_name (| globals, "block" |), "header" |);
      M.get_name (| globals, "chain" |)
    ],
    make_dict []
  |) in
    let apply_body_output :=
      M.call (|
        M.get_name (| globals, "apply_body" |),
        make_list [
          M.get_field (| M.get_name (| globals, "chain" |), "state" |);
          M.call (|
            M.get_name (| globals, "get_last_256_block_hashes" |),
            make_list [
              M.get_name (| globals, "chain" |)
            ],
            make_dict []
          |);
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "coinbase" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "number" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "gas_limit" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "timestamp" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "difficulty" |);
          M.get_field (| M.get_name (| globals, "block" |), "transactions" |);
          M.get_field (| M.get_name (| globals, "block" |), "ommers" |);
          M.get_field (| M.get_name (| globals, "chain" |), "chain_id" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "apply_body_output" |), "block_gas_used" |),
        M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "gas_used" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "apply_body_output" |), "transactions_root" |),
        M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "transactions_root" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "apply_body_output" |), "state_root" |),
        M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "state_root" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "apply_body_output" |), "receipt_root" |),
        M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "receipt_root" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "apply_body_output" |), "block_logs_bloom" |),
        M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "bloom" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "chain" |), "blocks" |), "append" |),
    make_list [
      M.get_name (| globals, "block" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, "chain" |), "blocks" |)
            ],
            make_dict []
          |),
          Constant.int 255
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, "chain" |), "blocks" |),
          M.get_subscript (| M.get_field (| M.get_name (| globals, "chain" |), "blocks" |), M.slice (| UnOp.sub (| Constant.int 255 |), Constant.None_ |) |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition validate_header : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "header"; "parent_header" ] |) in
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
    let parent_has_ommers :=
      Compare.not_eq (|
        M.get_field (| M.get_name (| globals, "parent_header" |), "ommers_hash" |),
        M.get_name (| globals, "EMPTY_OMMER_HASH" |)
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt (|
        M.get_field (| M.get_name (| globals, "header" |), "timestamp" |),
        M.get_field (| M.get_name (| globals, "parent_header" |), "timestamp" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "header" |), "number" |),
        BinOp.add (|
          M.get_field (| M.get_name (| globals, "parent_header" |), "number" |),
          Constant.int 1
        |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      M.call (|
        M.get_name (| globals, "check_gas_limit" |),
        make_list [
          M.get_field (| M.get_name (| globals, "header" |), "gas_limit" |);
          M.get_field (| M.get_name (| globals, "parent_header" |), "gas_limit" |)
        ],
        make_dict []
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt_e (|
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_field (| M.get_name (| globals, "header" |), "extra_data" |)
          ],
          make_dict []
        |),
        Constant.int 32
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let block_difficulty :=
      M.call (|
        M.get_name (| globals, "calculate_block_difficulty" |),
        make_list [
          M.get_field (| M.get_name (| globals, "header" |), "number" |);
          M.get_field (| M.get_name (| globals, "header" |), "timestamp" |);
          M.get_field (| M.get_name (| globals, "parent_header" |), "timestamp" |);
          M.get_field (| M.get_name (| globals, "parent_header" |), "difficulty" |);
          M.get_name (| globals, "parent_has_ommers" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "header" |), "difficulty" |),
        M.get_name (| globals, "block_difficulty" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let block_parent_hash :=
      M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
            make_list [
              M.get_name (| globals, "parent_header" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "header" |), "parent_hash" |),
        M.get_name (| globals, "block_parent_hash" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "validate_proof_of_work" |),
    make_list [
      M.get_name (| globals, "header" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition generate_header_hash_for_pow : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "header" ] |) in
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
    let header_data_without_pow_artefacts :=
      make_list [
        M.get_field (| M.get_name (| globals, "header" |), "parent_hash" |);
        M.get_field (| M.get_name (| globals, "header" |), "ommers_hash" |);
        M.get_field (| M.get_name (| globals, "header" |), "coinbase" |);
        M.get_field (| M.get_name (| globals, "header" |), "state_root" |);
        M.get_field (| M.get_name (| globals, "header" |), "transactions_root" |);
        M.get_field (| M.get_name (| globals, "header" |), "receipt_root" |);
        M.get_field (| M.get_name (| globals, "header" |), "bloom" |);
        M.get_field (| M.get_name (| globals, "header" |), "difficulty" |);
        M.get_field (| M.get_name (| globals, "header" |), "number" |);
        M.get_field (| M.get_name (| globals, "header" |), "gas_limit" |);
        M.get_field (| M.get_name (| globals, "header" |), "gas_used" |);
        M.get_field (| M.get_name (| globals, "header" |), "timestamp" |);
        M.get_field (| M.get_name (| globals, "header" |), "extra_data" |)
      ] in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_name (| globals, "rlp" |), "rlp_hash" |),
        make_list [
          M.get_name (| globals, "header_data_without_pow_artefacts" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition validate_proof_of_work : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "header" ] |) in
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
    let header_hash :=
      M.call (|
        M.get_name (| globals, "generate_header_hash_for_pow" |),
        make_list [
          M.get_name (| globals, "header" |)
        ],
        make_dict []
      |) in
    let cache :=
      M.call (|
        M.get_name (| globals, "generate_cache" |),
        make_list [
          M.get_field (| M.get_name (| globals, "header" |), "number" |)
        ],
        make_dict []
      |) in
    let _ := M.assign (|
      make_tuple [ M.get_name (| globals, "mix_digest" |); M.get_name (| globals, "result" |) ],
      M.call (|
        M.get_name (| globals, "hashimoto_light" |),
        make_list [
          M.get_name (| globals, "header_hash" |);
          M.get_field (| M.get_name (| globals, "header" |), "nonce" |);
          M.get_name (| globals, "cache" |);
          M.call (|
            M.get_name (| globals, "dataset_size" |),
            make_list [
              M.get_field (| M.get_name (| globals, "header" |), "number" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_name (| globals, "mix_digest" |),
        M.get_field (| M.get_name (| globals, "header" |), "mix_digest" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt_e (|
        M.call (|
          M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
          make_list [
            M.get_name (| globals, "result" |)
          ],
          make_dict []
        |),
        BinOp.floor_div (|
          M.get_name (| globals, "U256_CEIL_VALUE" |),
          M.get_field (| M.get_name (| globals, "header" |), "difficulty" |)
        |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    M.pure Constant.None_)).

Definition check_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx"; "gas_available"; "chain_id" ] |) in
    let _ := Constant.str "
    Check if the transaction is includable in the block.

    Parameters
    ----------
    tx :
        The transaction.
    gas_available :
        The gas remaining in the block.
    chain_id :
        The ID of the current chain.

    Returns
    -------
    sender_address :
        The sender of the transaction.

    Raises
    ------
    InvalidBlock :
        If the transaction is not includable.
    " in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt_e (|
        M.get_field (| M.get_name (| globals, "tx" |), "gas" |),
        M.get_name (| globals, "gas_available" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let sender_address :=
      M.call (|
        M.get_name (| globals, "recover_sender" |),
        make_list [
          M.get_name (| globals, "chain_id" |);
          M.get_name (| globals, "tx" |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.get_name (| globals, "sender_address" |)
    |) in
    M.pure Constant.None_)).

Definition make_receipt : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx"; "error"; "cumulative_gas_used"; "logs" ] |) in
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
    let receipt :=
      M.call (|
        M.get_name (| globals, "Receipt" |),
        make_list [],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.get_name (| globals, "receipt" |)
    |) in
    M.pure Constant.None_)).

Definition ApplyBodyOutput : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition apply_body : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "block_hashes"; "coinbase"; "block_number"; "block_gas_limit"; "block_time"; "block_difficulty"; "transactions"; "ommers"; "chain_id" ] |) in
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
    let gas_available :=
      M.get_name (| globals, "block_gas_limit" |) in
(* At stmt: unsupported node type: AnnAssign *)
(* At stmt: unsupported node type: AnnAssign *)
(* At stmt: unsupported node type: AnnAssign *)
    For make_tuple [ M.get_name (| globals, "i" |); M.get_name (| globals, "tx" |) ] in M.call (|
    M.get_name (| globals, "enumerate" |),
    make_list [
      M.get_name (| globals, "transactions" |)
    ],
    make_dict []
  |) do
      let _ := M.call (|
    M.get_name (| globals, "trie_set" |),
    make_list [
      M.get_name (| globals, "transactions_trie" |);
      M.call (|
        M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
        make_list [
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "i" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |);
      M.get_name (| globals, "tx" |)
    ],
    make_dict []
  |) in
      let sender_address :=
        M.call (|
          M.get_name (| globals, "check_transaction" |),
          make_list [
            M.get_name (| globals, "tx" |);
            M.get_name (| globals, "gas_available" |);
            M.get_name (| globals, "chain_id" |)
          ],
          make_dict []
        |) in
      let env :=
        M.call (|
          M.get_field (| M.get_name (| globals, "vm" |), "Environment" |),
          make_list [],
          make_dict []
        |) in
      let _ := M.assign (|
        make_tuple [ M.get_name (| globals, "gas_used" |); M.get_name (| globals, "logs" |); M.get_name (| globals, "error" |) ],
        M.call (|
          M.get_name (| globals, "process_transaction" |),
          make_list [
            M.get_name (| globals, "env" |);
            M.get_name (| globals, "tx" |)
          ],
          make_dict []
        |)
      |) in
      let gas_available := BinOp.sub
        M.get_name (| globals, "gas_used" |)
        M.get_name (| globals, "gas_used" |) in
      let receipt :=
        M.call (|
          M.get_name (| globals, "make_receipt" |),
          make_list [
            M.get_name (| globals, "tx" |);
            M.get_name (| globals, "error" |);
            BinOp.sub (|
              M.get_name (| globals, "block_gas_limit" |),
              M.get_name (| globals, "gas_available" |)
            |);
            M.get_name (| globals, "logs" |)
          ],
          make_dict []
        |) in
      let _ := M.call (|
    M.get_name (| globals, "trie_set" |),
    make_list [
      M.get_name (| globals, "receipts_trie" |);
      M.call (|
        M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
        make_list [
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "i" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |);
      M.get_name (| globals, "receipt" |)
    ],
    make_dict []
  |) in
      let block_logs := BinOp.add
        M.get_name (| globals, "logs" |)
        M.get_name (| globals, "logs" |) in
    EndFor.
    let _ := M.call (|
    M.get_name (| globals, "pay_rewards" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "block_number" |);
      M.get_name (| globals, "coinbase" |);
      M.get_name (| globals, "ommers" |)
    ],
    make_dict []
  |) in
    let block_gas_used :=
      BinOp.sub (|
        M.get_name (| globals, "block_gas_limit" |),
        M.get_name (| globals, "gas_available" |)
      |) in
    let block_logs_bloom :=
      M.call (|
        M.get_name (| globals, "logs_bloom" |),
        make_list [
          M.get_name (| globals, "block_logs" |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "ApplyBodyOutput" |),
        make_list [
          M.get_name (| globals, "block_gas_used" |);
          M.call (|
            M.get_name (| globals, "root" |),
            make_list [
              M.get_name (| globals, "transactions_trie" |)
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, "root" |),
            make_list [
              M.get_name (| globals, "receipts_trie" |)
            ],
            make_dict []
          |);
          M.get_name (| globals, "block_logs_bloom" |);
          M.call (|
            M.get_name (| globals, "state_root" |),
            make_list [
              M.get_name (| globals, "state" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition validate_ommers : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "ommers"; "block_header"; "chain" ] |) in
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
    let block_hash :=
      M.call (|
        M.get_field (| M.get_name (| globals, "rlp" |), "rlp_hash" |),
        make_list [
          M.get_name (| globals, "block_header" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_field (| M.get_name (| globals, "rlp" |), "rlp_hash" |),
          make_list [
            M.get_name (| globals, "ommers" |)
          ],
          make_dict []
        |),
        M.get_field (| M.get_name (| globals, "block_header" |), "ommers_hash" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "ommers" |)
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
    For M.get_name (| globals, "ommer" |) in M.get_name (| globals, "ommers" |) do
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      BoolOp.and (|
        Compare.lt_e (|
          Constant.int 1,
          M.get_field (| M.get_name (| globals, "ommer" |), "number" |)
        |),
        ltac:(M.monadic (
          Compare.lt (|
            M.get_field (| M.get_name (| globals, "ommer" |), "number" |),
            M.get_field (| M.get_name (| globals, "block_header" |), "number" |)
          |)
        ))
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
      let ommer_parent_header :=
        M.get_field (| M.get_subscript (| M.get_field (| M.get_name (| globals, "chain" |), "blocks" |), BinOp.sub (|
          UnOp.sub (| BinOp.sub (|
            M.get_field (| M.get_name (| globals, "block_header" |), "number" |),
            M.get_field (| M.get_name (| globals, "ommer" |), "number" |)
          |) |),
          Constant.int 1
        |) |), "header" |) in
      let _ := M.call (|
    M.get_name (| globals, "validate_header" |),
    make_list [
      M.get_name (| globals, "ommer" |);
      M.get_name (| globals, "ommer_parent_header" |)
    ],
    make_dict []
  |) in
    EndFor.
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt_e (|
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "ommers" |)
          ],
          make_dict []
        |),
        Constant.int 2
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let ommers_hashes :=
      Constant.str "(* At expr: unsupported node type: ListComp *)" in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "ommers_hashes" |)
          ],
          make_dict []
        |),
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.call (|
              M.get_name (| globals, "set" |),
              make_list [
                M.get_name (| globals, "ommers_hashes" |)
              ],
              make_dict []
            |)
          ],
          make_dict []
        |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let recent_canonical_blocks :=
      M.get_subscript (| M.get_field (| M.get_name (| globals, "chain" |), "blocks" |), M.slice (| UnOp.sub (| BinOp.add (|
        M.get_name (| globals, "MAX_OMMER_DEPTH" |),
        Constant.int 1
      |) |), Constant.None_ |) |) in
    let recent_canonical_block_hashes :=
      Constant.str "(* At expr: unsupported node type: SetComp *)" in
(* At stmt: unsupported node type: AnnAssign *)
    For M.get_name (| globals, "block" |) in M.get_name (| globals, "recent_canonical_blocks" |) do
      let recent_ommers_hashes :=
        M.call (|
          M.get_field (| M.get_name (| globals, "recent_ommers_hashes" |), "union" |),
          make_list [
            Constant.str "(* At expr: unsupported node type: SetComp *)"
          ],
          make_dict []
        |) in
    EndFor.
    For make_tuple [ M.get_name (| globals, "ommer_index" |); M.get_name (| globals, "ommer" |) ] in M.call (|
    M.get_name (| globals, "enumerate" |),
    make_list [
      M.get_name (| globals, "ommers" |)
    ],
    make_dict []
  |) do
      let ommer_hash :=
        M.get_subscript (| M.get_name (| globals, "ommers_hashes" |), M.get_name (| globals, "ommer_index" |) |) in
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.not_eq (|
        M.get_name (| globals, "ommer_hash" |),
        M.get_name (| globals, "block_hash" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.not_in (|
        M.get_name (| globals, "ommer_hash" |),
        M.get_name (| globals, "recent_canonical_block_hashes" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.not_in (|
        M.get_name (| globals, "ommer_hash" |),
        M.get_name (| globals, "recent_ommers_hashes" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
      let ommer_age :=
        BinOp.sub (|
          M.get_field (| M.get_name (| globals, "block_header" |), "number" |),
          M.get_field (| M.get_name (| globals, "ommer" |), "number" |)
        |) in
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      BoolOp.and (|
        Compare.lt_e (|
          Constant.int 1,
          M.get_name (| globals, "ommer_age" |)
        |),
        ltac:(M.monadic (
          Compare.lt_e (|
            M.get_name (| globals, "ommer_age" |),
            M.get_name (| globals, "MAX_OMMER_DEPTH" |)
          |)
        ))
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.in (|
        M.get_field (| M.get_name (| globals, "ommer" |), "parent_hash" |),
        M.get_name (| globals, "recent_canonical_block_hashes" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.not_eq (|
        M.get_field (| M.get_name (| globals, "ommer" |), "parent_hash" |),
        M.get_field (| M.get_name (| globals, "block_header" |), "parent_hash" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    EndFor.
    M.pure Constant.None_)).

Definition pay_rewards : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "state"; "block_number"; "coinbase"; "ommers" ] |) in
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
    let miner_reward :=
      BinOp.add (|
        M.get_name (| globals, "BLOCK_REWARD" |),
        BinOp.mult (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "ommers" |)
            ],
            make_dict []
          |),
          BinOp.floor_div (|
            M.get_name (| globals, "BLOCK_REWARD" |),
            Constant.int 32
          |)
        |)
      |) in
    let _ := M.call (|
    M.get_name (| globals, "create_ether" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_name (| globals, "coinbase" |);
      M.get_name (| globals, "miner_reward" |)
    ],
    make_dict []
  |) in
    For M.get_name (| globals, "ommer" |) in M.get_name (| globals, "ommers" |) do
      let ommer_age :=
        M.call (|
          M.get_name (| globals, "U256" |),
          make_list [
            BinOp.sub (|
              M.get_name (| globals, "block_number" |),
              M.get_field (| M.get_name (| globals, "ommer" |), "number" |)
            |)
          ],
          make_dict []
        |) in
      let ommer_miner_reward :=
        BinOp.floor_div (|
          BinOp.mult (|
            BinOp.sub (|
              Constant.int 8,
              M.get_name (| globals, "ommer_age" |)
            |),
            M.get_name (| globals, "BLOCK_REWARD" |)
          |),
          Constant.int 8
        |) in
      let _ := M.call (|
    M.get_name (| globals, "create_ether" |),
    make_list [
      M.get_name (| globals, "state" |);
      M.get_field (| M.get_name (| globals, "ommer" |), "coinbase" |);
      M.get_name (| globals, "ommer_miner_reward" |)
    ],
    make_dict []
  |) in
    EndFor.
    M.pure Constant.None_)).

Definition process_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "env"; "tx" ] |) in
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
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      M.call (|
        M.get_name (| globals, "validate_transaction" |),
        make_list [
          M.get_name (| globals, "tx" |)
        ],
        make_dict []
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let sender :=
      M.get_field (| M.get_name (| globals, "env" |), "origin" |) in
    let sender_account :=
      M.call (|
        M.get_name (| globals, "get_account" |),
        make_list [
          M.get_field (| M.get_name (| globals, "env" |), "state" |);
          M.get_name (| globals, "sender" |)
        ],
        make_dict []
      |) in
    let gas_fee :=
      BinOp.mult (|
        M.get_field (| M.get_name (| globals, "tx" |), "gas" |),
        M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |)
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "sender_account" |), "nonce" |),
        M.get_field (| M.get_name (| globals, "tx" |), "nonce" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt_e (|
        M.get_field (| M.get_name (| globals, "sender_account" |), "balance" |),
        BinOp.add (|
          M.get_name (| globals, "gas_fee" |),
          M.get_field (| M.get_name (| globals, "tx" |), "value" |)
        |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "sender_account" |), "code" |),
        M.call (|
          M.get_name (| globals, "bytearray" |),
          make_list [],
          make_dict []
        |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let gas :=
      BinOp.sub (|
        M.get_field (| M.get_name (| globals, "tx" |), "gas" |),
        M.call (|
          M.get_name (| globals, "calculate_intrinsic_cost" |),
          make_list [
            M.get_name (| globals, "tx" |)
          ],
          make_dict []
        |)
      |) in
    let _ := M.call (|
    M.get_name (| globals, "increment_nonce" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_name (| globals, "sender" |)
    ],
    make_dict []
  |) in
    let sender_balance_after_gas_fee :=
      BinOp.sub (|
        M.get_field (| M.get_name (| globals, "sender_account" |), "balance" |),
        M.get_name (| globals, "gas_fee" |)
      |) in
    let _ := M.call (|
    M.get_name (| globals, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_name (| globals, "sender" |);
      M.get_name (| globals, "sender_balance_after_gas_fee" |)
    ],
    make_dict []
  |) in
    let message :=
      M.call (|
        M.get_name (| globals, "prepare_message" |),
        make_list [
          M.get_name (| globals, "sender" |);
          M.get_field (| M.get_name (| globals, "tx" |), "to" |);
          M.get_field (| M.get_name (| globals, "tx" |), "value" |);
          M.get_field (| M.get_name (| globals, "tx" |), "data" |);
          M.get_name (| globals, "gas" |);
          M.get_name (| globals, "env" |)
        ],
        make_dict []
      |) in
    let output :=
      M.call (|
        M.get_name (| globals, "process_message_call" |),
        make_list [
          M.get_name (| globals, "message" |);
          M.get_name (| globals, "env" |)
        ],
        make_dict []
      |) in
    let gas_used :=
      BinOp.sub (|
        M.get_field (| M.get_name (| globals, "tx" |), "gas" |),
        M.get_field (| M.get_name (| globals, "output" |), "gas_left" |)
      |) in
    let gas_refund :=
      M.call (|
        M.get_name (| globals, "min" |),
        make_list [
          BinOp.floor_div (|
            M.get_name (| globals, "gas_used" |),
            Constant.int 2
          |);
          M.get_field (| M.get_name (| globals, "output" |), "refund_counter" |)
        ],
        make_dict []
      |) in
    let gas_refund_amount :=
      BinOp.mult (|
        BinOp.add (|
          M.get_field (| M.get_name (| globals, "output" |), "gas_left" |),
          M.get_name (| globals, "gas_refund" |)
        |),
        M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |)
      |) in
    let transaction_fee :=
      BinOp.mult (|
        BinOp.sub (|
          BinOp.sub (|
            M.get_field (| M.get_name (| globals, "tx" |), "gas" |),
            M.get_field (| M.get_name (| globals, "output" |), "gas_left" |)
          |),
          M.get_name (| globals, "gas_refund" |)
        |),
        M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |)
      |) in
    let total_gas_used :=
      BinOp.sub (|
        M.get_name (| globals, "gas_used" |),
        M.get_name (| globals, "gas_refund" |)
      |) in
    let sender_balance_after_refund :=
      BinOp.add (|
        M.get_field (| M.call (|
          M.get_name (| globals, "get_account" |),
          make_list [
            M.get_field (| M.get_name (| globals, "env" |), "state" |);
            M.get_name (| globals, "sender" |)
          ],
          make_dict []
        |), "balance" |),
        M.get_name (| globals, "gas_refund_amount" |)
      |) in
    let _ := M.call (|
    M.get_name (| globals, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_name (| globals, "sender" |);
      M.get_name (| globals, "sender_balance_after_refund" |)
    ],
    make_dict []
  |) in
    let coinbase_balance_after_mining_fee :=
      BinOp.add (|
        M.get_field (| M.call (|
          M.get_name (| globals, "get_account" |),
          make_list [
            M.get_field (| M.get_name (| globals, "env" |), "state" |);
            M.get_field (| M.get_name (| globals, "env" |), "coinbase" |)
          ],
          make_dict []
        |), "balance" |),
        M.get_name (| globals, "transaction_fee" |)
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_name (| globals, "coinbase_balance_after_mining_fee" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "set_account_balance" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, "env" |), "coinbase" |);
      M.get_name (| globals, "coinbase_balance_after_mining_fee" |)
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
              M.get_name (| globals, "account_exists_and_is_empty" |),
              make_list [
                M.get_field (| M.get_name (| globals, "env" |), "state" |);
                M.get_field (| M.get_name (| globals, "env" |), "coinbase" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.call (|
    M.get_name (| globals, "destroy_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_field (| M.get_name (| globals, "env" |), "coinbase" |)
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
    For M.get_name (| globals, "address" |) in M.get_field (| M.get_name (| globals, "output" |), "accounts_to_delete" |) do
      let _ := M.call (|
    M.get_name (| globals, "destroy_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_name (| globals, "address" |)
    ],
    make_dict []
  |) in
    EndFor.
    For M.get_name (| globals, "address" |) in M.get_field (| M.get_name (| globals, "output" |), "touched_accounts" |) do
      let _ :=
        (* if *)
        M.if_then_else (|
          M.call (|
            M.get_name (| globals, "account_exists_and_is_empty" |),
            make_list [
              M.get_field (| M.get_name (| globals, "env" |), "state" |);
              M.get_name (| globals, "address" |)
            ],
            make_dict []
          |),
        (* then *)
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_name (| globals, "destroy_account" |),
    make_list [
      M.get_field (| M.get_name (| globals, "env" |), "state" |);
      M.get_name (| globals, "address" |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          M.pure Constant.None_
        )) |) in
    EndFor.
    let _ := M.return_ (|
      make_tuple [ M.get_name (| globals, "total_gas_used" |); M.get_field (| M.get_name (| globals, "output" |), "logs" |); M.get_field (| M.get_name (| globals, "output" |), "error" |) ]
    |) in
    M.pure Constant.None_)).

Definition validate_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx" ] |) in
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
            M.get_name (| globals, "calculate_intrinsic_cost" |),
            make_list [
              M.get_name (| globals, "tx" |)
            ],
            make_dict []
          |),
          M.get_field (| M.get_name (| globals, "tx" |), "gas" |)
        |),
        ltac:(M.monadic (
          Compare.lt (|
            M.get_field (| M.get_name (| globals, "tx" |), "nonce" |),
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

Definition calculate_intrinsic_cost : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx" ] |) in
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
    let data_cost :=
      Constant.int 0 in
    For M.get_name (| globals, "byte" |) in M.get_field (| M.get_name (| globals, "tx" |), "data" |) do
      let _ :=
        (* if *)
        M.if_then_else (|
          Compare.eq (|
            M.get_name (| globals, "byte" |),
            Constant.int 0
          |),
        (* then *)
        ltac:(M.monadic (
          let data_cost := BinOp.add
            M.get_name (| globals, "TX_DATA_COST_PER_ZERO" |)
            M.get_name (| globals, "TX_DATA_COST_PER_ZERO" |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          let data_cost := BinOp.add
            M.get_name (| globals, "TX_DATA_COST_PER_NON_ZERO" |)
            M.get_name (| globals, "TX_DATA_COST_PER_NON_ZERO" |) in
          M.pure Constant.None_
        )) |) in
    EndFor.
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_field (| M.get_name (| globals, "tx" |), "to" |),
          M.call (|
            M.get_name (| globals, "Bytes0" |),
            make_list [
              Constant.bytes ""
            ],
            make_dict []
          |)
        |),
      (* then *)
      ltac:(M.monadic (
        let create_cost :=
          M.get_name (| globals, "TX_CREATE_COST" |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let create_cost :=
          Constant.int 0 in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          BinOp.add (|
            BinOp.add (|
              M.get_name (| globals, "TX_BASE_COST" |),
              M.get_name (| globals, "data_cost" |)
            |),
            M.get_name (| globals, "create_cost" |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition recover_sender : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "chain_id"; "tx" ] |) in
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
      make_tuple [ M.get_name (| globals, "v" |); M.get_name (| globals, "r" |); M.get_name (| globals, "s" |) ],
      make_tuple [ M.get_field (| M.get_name (| globals, "tx" |), "v" |); M.get_field (| M.get_name (| globals, "tx" |), "r" |); M.get_field (| M.get_name (| globals, "tx" |), "s" |) ]
    |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      BoolOp.and (|
        Compare.lt (|
          Constant.int 0,
          M.get_name (| globals, "r" |)
        |),
        ltac:(M.monadic (
          Compare.lt (|
            M.get_name (| globals, "r" |),
            M.get_name (| globals, "SECP256K1N" |)
          |)
        ))
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      BoolOp.and (|
        Compare.lt (|
          Constant.int 0,
          M.get_name (| globals, "s" |)
        |),
        ltac:(M.monadic (
          Compare.lt_e (|
            M.get_name (| globals, "s" |),
            BinOp.floor_div (|
              M.get_name (| globals, "SECP256K1N" |),
              Constant.int 2
            |)
          |)
        ))
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.eq (|
            M.get_name (| globals, "v" |),
            Constant.int 27
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_name (| globals, "v" |),
              Constant.int 28
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let public_key :=
          M.call (|
            M.get_name (| globals, "secp256k1_recover" |),
            make_list [
              M.get_name (| globals, "r" |);
              M.get_name (| globals, "s" |);
              BinOp.sub (|
                M.get_name (| globals, "v" |),
                Constant.int 27
              |);
              M.call (|
                M.get_name (| globals, "signing_hash_pre155" |),
                make_list [
                  M.get_name (| globals, "tx" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      BoolOp.or (|
        Compare.eq (|
          M.get_name (| globals, "v" |),
          BinOp.add (|
            Constant.int 35,
            BinOp.mult (|
              M.get_name (| globals, "chain_id" |),
              Constant.int 2
            |)
          |)
        |),
        ltac:(M.monadic (
          Compare.eq (|
            M.get_name (| globals, "v" |),
            BinOp.add (|
              Constant.int 36,
              BinOp.mult (|
                M.get_name (| globals, "chain_id" |),
                Constant.int 2
              |)
            |)
          |)
        ))
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
        let public_key :=
          M.call (|
            M.get_name (| globals, "secp256k1_recover" |),
            make_list [
              M.get_name (| globals, "r" |);
              M.get_name (| globals, "s" |);
              BinOp.sub (|
                BinOp.sub (|
                  M.get_name (| globals, "v" |),
                  Constant.int 35
                |),
                BinOp.mult (|
                  M.get_name (| globals, "chain_id" |),
                  Constant.int 2
                |)
              |);
              M.call (|
                M.get_name (| globals, "signing_hash_155" |),
                make_list [
                  M.get_name (| globals, "tx" |);
                  M.get_name (| globals, "chain_id" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Address" |),
        make_list [
          M.get_subscript (| M.call (|
            M.get_name (| globals, "keccak256" |),
            make_list [
              M.get_name (| globals, "public_key" |)
            ],
            make_dict []
          |), M.slice (| Constant.int 12, Constant.int 32 |) |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition signing_hash_pre155 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx" ] |) in
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
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
            make_list [
              make_tuple [ M.get_field (| M.get_name (| globals, "tx" |), "nonce" |); M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |); M.get_field (| M.get_name (| globals, "tx" |), "gas" |); M.get_field (| M.get_name (| globals, "tx" |), "to" |); M.get_field (| M.get_name (| globals, "tx" |), "value" |); M.get_field (| M.get_name (| globals, "tx" |), "data" |) ]
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition signing_hash_155 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx"; "chain_id" ] |) in
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
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
            make_list [
              make_tuple [ M.get_field (| M.get_name (| globals, "tx" |), "nonce" |); M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |); M.get_field (| M.get_name (| globals, "tx" |), "gas" |); M.get_field (| M.get_name (| globals, "tx" |), "to" |); M.get_field (| M.get_name (| globals, "tx" |), "value" |); M.get_field (| M.get_name (| globals, "tx" |), "data" |); M.get_name (| globals, "chain_id" |); M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  Constant.int 0
                ],
                make_dict []
              |); M.call (|
                M.get_name (| globals, "Uint" |),
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

Definition compute_header_hash : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "header" ] |) in
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
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
            make_list [
              M.get_name (| globals, "header" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition check_gas_limit : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "gas_limit"; "parent_gas_limit" ] |) in
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
    let max_adjustment_delta :=
      BinOp.floor_div (|
        M.get_name (| globals, "parent_gas_limit" |),
        M.get_name (| globals, "GAS_LIMIT_ADJUSTMENT_FACTOR" |)
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt_e (|
          M.get_name (| globals, "gas_limit" |),
          BinOp.add (|
            M.get_name (| globals, "parent_gas_limit" |),
            M.get_name (| globals, "max_adjustment_delta" |)
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
          M.get_name (| globals, "gas_limit" |),
          BinOp.sub (|
            M.get_name (| globals, "parent_gas_limit" |),
            M.get_name (| globals, "max_adjustment_delta" |)
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
          M.get_name (| globals, "gas_limit" |),
          M.get_name (| globals, "GAS_LIMIT_MINIMUM" |)
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

Definition calculate_block_difficulty : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "block_number"; "block_timestamp"; "parent_timestamp"; "parent_difficulty"; "parent_has_ommers" ] |) in
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
    let offset :=
      BinOp.mult (|
        BinOp.floor_div (|
          M.call (|
            M.get_name (| globals, "int" |),
            make_list [
              M.get_name (| globals, "parent_difficulty" |)
            ],
            make_dict []
          |),
          Constant.int 2048
        |),
        M.call (|
          M.get_name (| globals, "max" |),
          make_list [
            BinOp.sub (|
                            (* if *)
              M.if_then_else (|
                M.get_name (| globals, "parent_has_ommers" |),
              (* then *)
              ltac:(M.monadic (
Constant.int 2
              (* else *)
              )), ltac:(M.monadic (
Constant.int 1
              )) |),
              BinOp.floor_div (|
                M.call (|
                  M.get_name (| globals, "int" |),
                  make_list [
                    BinOp.sub (|
                      M.get_name (| globals, "block_timestamp" |),
                      M.get_name (| globals, "parent_timestamp" |)
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
      |) in
    let difficulty :=
      BinOp.add (|
        M.call (|
          M.get_name (| globals, "int" |),
          make_list [
            M.get_name (| globals, "parent_difficulty" |)
          ],
          make_dict []
        |),
        M.get_name (| globals, "offset" |)
      |) in
    let num_bomb_periods :=
      BinOp.sub (|
        BinOp.floor_div (|
          BinOp.sub (|
            M.call (|
              M.get_name (| globals, "int" |),
              make_list [
                M.get_name (| globals, "block_number" |)
              ],
              make_dict []
            |),
            M.get_name (| globals, "BOMB_DELAY_BLOCKS" |)
          |),
          Constant.int 100000
        |),
        Constant.int 2
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt_e (|
          M.get_name (| globals, "num_bomb_periods" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let difficulty := BinOp.add
          BinOp.pow (|
    Constant.int 2,
    M.get_name (| globals, "num_bomb_periods" |)
  |)
          BinOp.pow (|
    Constant.int 2,
    M.get_name (| globals, "num_bomb_periods" |)
  |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.call (|
            M.get_name (| globals, "max" |),
            make_list [
              M.get_name (| globals, "difficulty" |);
              M.get_name (| globals, "MINIMUM_DIFFICULTY" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).