Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.paris.fork".

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

Axiom dataclasses_imports :
  AreImported globals "dataclasses" [ "dataclass" ].

Axiom typing_imports :
  AreImported globals "typing" [ "List"; "Optional"; "Tuple"; "Union" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "Bytes0"; "Bytes32" ].

Axiom ethereum_crypto_elliptic_curve_imports :
  AreImported globals "ethereum.crypto.elliptic_curve" [ "SECP256K1N"; "secp256k1_recover" ].

Axiom ethereum_crypto_hash_imports :
  AreImported globals "ethereum.crypto.hash" [ "Hash32"; "keccak256" ].

Axiom ethereum_exceptions_imports :
  AreImported globals "ethereum.exceptions" [ "InvalidBlock" ].

Axiom ethereum_utils_ensure_imports :
  AreImported globals "ethereum.utils.ensure" [ "ensure" ].

Axiom ethereum_imports :
  AreImported globals "ethereum" [ "rlp" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "U64"; "U256"; "Bytes"; "Uint" ].

Axiom ethereum_paris_imports :
  AreImported globals "ethereum.paris" [ "vm" ].

Axiom ethereum_paris_blocks_imports :
  AreImported globals "ethereum.paris.blocks" [ "Block"; "Header"; "Log"; "Receipt" ].

Axiom ethereum_paris_bloom_imports :
  AreImported globals "ethereum.paris.bloom" [ "logs_bloom" ].

Axiom ethereum_paris_fork_types_imports :
  AreImported globals "ethereum.paris.fork_types" [ "Address"; "Bloom"; "Root" ].

Axiom ethereum_paris_state_imports :
  AreImported globals "ethereum.paris.state" [ "State"; "account_exists_and_is_empty"; "destroy_account"; "get_account"; "increment_nonce"; "set_account_balance"; "state_root" ].

Axiom ethereum_paris_transactions_imports :
  AreImported globals "ethereum.paris.transactions" [ "TX_ACCESS_LIST_ADDRESS_COST"; "TX_ACCESS_LIST_STORAGE_KEY_COST"; "TX_BASE_COST"; "TX_CREATE_COST"; "TX_DATA_COST_PER_NON_ZERO"; "TX_DATA_COST_PER_ZERO"; "AccessListTransaction"; "FeeMarketTransaction"; "LegacyTransaction"; "Transaction"; "decode_transaction"; "encode_transaction" ].

Axiom ethereum_paris_trie_imports :
  AreImported globals "ethereum.paris.trie" [ "Trie"; "root"; "trie_set" ].

Axiom ethereum_paris_utils_message_imports :
  AreImported globals "ethereum.paris.utils.message" [ "prepare_message" ].

Axiom ethereum_paris_vm_interpreter_imports :
  AreImported globals "ethereum.paris.vm.interpreter" [ "process_message_call" ].

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
      M.slice (|
        M.get_field (| M.get_name (| globals, "chain" |), "blocks" |),
        UnOp.sub (| Constant.int 255 |),
        Constant.None_,
        Constant.None_
      |) in
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
    let _ :=
      M.for_ (|
        M.get_name (| globals, "block" |),
        M.get_name (| globals, "recent_blocks" |),
        ltac:(M.monadic (
          let prev_block_hash :=
            M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "parent_hash" |) in
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, "recent_block_hashes" |), "append" |),
    make_list [
      M.get_name (| globals, "prev_block_hash" |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let most_recent_block_hash :=
      M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
            make_list [
              M.get_field (| M.get_subscript (|
                M.get_name (| globals, "recent_blocks" |),
                UnOp.sub (| Constant.int 1 |)
              |), "header" |)
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
      M.get_field (| M.get_subscript (|
        M.get_field (| M.get_name (| globals, "chain" |), "blocks" |),
        UnOp.sub (| Constant.int 1 |)
      |), "header" |) in
    let _ := M.call (|
    M.get_name (| globals, "validate_header" |),
    make_list [
      M.get_field (| M.get_name (| globals, "block" |), "header" |);
      M.get_name (| globals, "parent_header" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "block" |), "ommers" |),
        make_tuple [  ]
      |);
      M.get_name (| globals, "InvalidBlock" |)
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
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "base_fee_per_gas" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "gas_limit" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "timestamp" |);
          M.get_field (| M.get_field (| M.get_name (| globals, "block" |), "header" |), "prev_randao" |);
          M.get_field (| M.get_name (| globals, "block" |), "transactions" |);
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
          M.slice (|
            M.get_field (| M.get_name (| globals, "chain" |), "blocks" |),
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

Definition calculate_base_fee_per_gas : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "block_gas_limit"; "parent_gas_limit"; "parent_gas_used"; "parent_base_fee_per_gas" ] |) in
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

    Returns
    -------
    base_fee_per_gas : `Uint`
        Base fee per gas for the block.
    " in
    let parent_gas_target :=
      BinOp.floor_div (|
        M.get_name (| globals, "parent_gas_limit" |),
        M.get_name (| globals, "ELASTICITY_MULTIPLIER" |)
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      M.call (|
        M.get_name (| globals, "check_gas_limit" |),
        make_list [
          M.get_name (| globals, "block_gas_limit" |);
          M.get_name (| globals, "parent_gas_limit" |)
        ],
        make_dict []
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, "parent_gas_used" |),
          M.get_name (| globals, "parent_gas_target" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let expected_base_fee_per_gas :=
          M.get_name (| globals, "parent_base_fee_per_gas" |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt (|
              M.get_name (| globals, "parent_gas_used" |),
              M.get_name (| globals, "parent_gas_target" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let gas_used_delta :=
              BinOp.sub (|
                M.get_name (| globals, "parent_gas_used" |),
                M.get_name (| globals, "parent_gas_target" |)
              |) in
            let parent_fee_gas_delta :=
              BinOp.mult (|
                M.get_name (| globals, "parent_base_fee_per_gas" |),
                M.get_name (| globals, "gas_used_delta" |)
              |) in
            let target_fee_gas_delta :=
              BinOp.floor_div (|
                M.get_name (| globals, "parent_fee_gas_delta" |),
                M.get_name (| globals, "parent_gas_target" |)
              |) in
            let base_fee_per_gas_delta :=
              M.call (|
                M.get_name (| globals, "max" |),
                make_list [
                  BinOp.floor_div (|
                    M.get_name (| globals, "target_fee_gas_delta" |),
                    M.get_name (| globals, "BASE_FEE_MAX_CHANGE_DENOMINATOR" |)
                  |);
                  Constant.int 1
                ],
                make_dict []
              |) in
            let expected_base_fee_per_gas :=
              BinOp.add (|
                M.get_name (| globals, "parent_base_fee_per_gas" |),
                M.get_name (| globals, "base_fee_per_gas_delta" |)
              |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let gas_used_delta :=
              BinOp.sub (|
                M.get_name (| globals, "parent_gas_target" |),
                M.get_name (| globals, "parent_gas_used" |)
              |) in
            let parent_fee_gas_delta :=
              BinOp.mult (|
                M.get_name (| globals, "parent_base_fee_per_gas" |),
                M.get_name (| globals, "gas_used_delta" |)
              |) in
            let target_fee_gas_delta :=
              BinOp.floor_div (|
                M.get_name (| globals, "parent_fee_gas_delta" |),
                M.get_name (| globals, "parent_gas_target" |)
              |) in
            let base_fee_per_gas_delta :=
              BinOp.floor_div (|
                M.get_name (| globals, "target_fee_gas_delta" |),
                M.get_name (| globals, "BASE_FEE_MAX_CHANGE_DENOMINATOR" |)
              |) in
            let expected_base_fee_per_gas :=
              BinOp.sub (|
                M.get_name (| globals, "parent_base_fee_per_gas" |),
                M.get_name (| globals, "base_fee_per_gas_delta" |)
              |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          M.get_name (| globals, "expected_base_fee_per_gas" |)
        ],
        make_dict []
      |)
    |) in
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
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.lt_e (|
        M.get_field (| M.get_name (| globals, "header" |), "gas_used" |),
        M.get_field (| M.get_name (| globals, "header" |), "gas_limit" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let expected_base_fee_per_gas :=
      M.call (|
        M.get_name (| globals, "calculate_base_fee_per_gas" |),
        make_list [
          M.get_field (| M.get_name (| globals, "header" |), "gas_limit" |);
          M.get_field (| M.get_name (| globals, "parent_header" |), "gas_limit" |);
          M.get_field (| M.get_name (| globals, "parent_header" |), "gas_used" |);
          M.get_field (| M.get_name (| globals, "parent_header" |), "base_fee_per_gas" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_name (| globals, "expected_base_fee_per_gas" |),
        M.get_field (| M.get_name (| globals, "header" |), "base_fee_per_gas" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
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
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "header" |), "difficulty" |),
        Constant.int 0
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "header" |), "nonce" |),
        Constant.bytes "0000000000000000"
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.get_field (| M.get_name (| globals, "header" |), "ommers_hash" |),
        M.get_name (| globals, "EMPTY_OMMER_HASH" |)
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
    M.pure Constant.None_)).

Definition check_transaction : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx"; "base_fee_per_gas"; "gas_available"; "chain_id" ] |) in
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
        let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt_e (|
        M.get_field (| M.get_name (| globals, "tx" |), "max_fee_per_gas" |),
        M.get_field (| M.get_name (| globals, "tx" |), "max_priority_fee_per_gas" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
        let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt_e (|
        M.get_field (| M.get_name (| globals, "tx" |), "max_fee_per_gas" |),
        M.get_name (| globals, "base_fee_per_gas" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
        let priority_fee_per_gas :=
          M.call (|
            M.get_name (| globals, "min" |),
            make_list [
              M.get_field (| M.get_name (| globals, "tx" |), "max_priority_fee_per_gas" |);
              BinOp.sub (|
                M.get_field (| M.get_name (| globals, "tx" |), "max_fee_per_gas" |),
                M.get_name (| globals, "base_fee_per_gas" |)
              |)
            ],
            make_dict []
          |) in
        let effective_gas_price :=
          BinOp.add (|
            M.get_name (| globals, "priority_fee_per_gas" |),
            M.get_name (| globals, "base_fee_per_gas" |)
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.gt_e (|
        M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |),
        M.get_name (| globals, "base_fee_per_gas" |)
      |);
      M.get_name (| globals, "InvalidBlock" |)
    ],
    make_dict []
  |) in
        let effective_gas_price :=
          M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      make_tuple [ M.get_name (| globals, "sender_address" |); M.get_name (| globals, "effective_gas_price" |) ]
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
        The error from the execution if any.
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
                M.get_name (| globals, "receipt" |)
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
                    M.get_name (| globals, "receipt" |)
                  ],
                  make_dict []
                |)
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.return_ (|
              M.get_name (| globals, "receipt" |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
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
    let _ := M.set_locals (| args, kwargs, [ "state"; "block_hashes"; "coinbase"; "block_number"; "base_fee_per_gas"; "block_gas_limit"; "block_time"; "prev_randao"; "transactions"; "chain_id" ] |) in
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
    prev_randao :
        The previous randao from the beacon chain.
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
    let _ :=
      M.for_ (|
        make_tuple [ M.get_name (| globals, "i" |); M.get_name (| globals, "tx" |) ],
        M.call (|
      M.get_name (| globals, "enumerate" |),
      make_list [
        M.call (|
          M.get_name (| globals, "map" |),
          make_list [
            M.get_name (| globals, "decode_transaction" |);
            M.get_name (| globals, "transactions" |)
          ],
          make_dict []
        |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
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
      M.call (|
        M.get_name (| globals, "encode_transaction" |),
        make_list [
          M.get_name (| globals, "tx" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, "sender_address" |); M.get_name (| globals, "effective_gas_price" |) ],
            M.call (|
              M.get_name (| globals, "check_transaction" |),
              make_list [
                M.get_name (| globals, "tx" |);
                M.get_name (| globals, "base_fee_per_gas" |);
                M.get_name (| globals, "gas_available" |);
                M.get_name (| globals, "chain_id" |)
              ],
              make_dict []
            |)
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
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
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
        let max_gas_fee :=
          BinOp.mult (|
            M.get_field (| M.get_name (| globals, "tx" |), "gas" |),
            M.get_field (| M.get_name (| globals, "tx" |), "max_fee_per_gas" |)
          |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let max_gas_fee :=
          BinOp.mult (|
            M.get_field (| M.get_name (| globals, "tx" |), "gas" |),
            M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |)
          |) in
        M.pure Constant.None_
      )) |) in
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
          M.get_name (| globals, "max_gas_fee" |),
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
    let effective_gas_fee :=
      BinOp.mult (|
        M.get_field (| M.get_name (| globals, "tx" |), "gas" |),
        M.get_field (| M.get_name (| globals, "env" |), "gas_price" |)
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
        M.get_name (| globals, "effective_gas_fee" |)
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
    let preaccessed_addresses :=
      M.call (|
        M.get_name (| globals, "set" |),
        make_list [],
        make_dict []
      |) in
    let preaccessed_storage_keys :=
      M.call (|
        M.get_name (| globals, "set" |),
        make_list [],
        make_dict []
      |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "isinstance" |),
          make_list [
            M.get_name (| globals, "tx" |);
            make_tuple [ M.get_name (| globals, "AccessListTransaction" |); M.get_name (| globals, "FeeMarketTransaction" |) ]
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          M.for_ (|
            make_tuple [ M.get_name (| globals, "address" |); M.get_name (| globals, "keys" |) ],
            M.get_field (| M.get_name (| globals, "tx" |), "access_list" |),
            ltac:(M.monadic (
              let _ := M.call (|
    M.get_field (| M.get_name (| globals, "preaccessed_addresses" |), "add" |),
    make_list [
      M.get_name (| globals, "address" |)
    ],
    make_dict []
  |) in
              let _ :=
                M.for_ (|
                  M.get_name (| globals, "key" |),
                  M.get_name (| globals, "keys" |),
                  ltac:(M.monadic (
                    let _ := M.call (|
    M.get_field (| M.get_name (| globals, "preaccessed_storage_keys" |), "add" |),
    make_list [
      make_tuple [ M.get_name (| globals, "address" |); M.get_name (| globals, "key" |) ]
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
            Constant.int 5
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
        M.get_field (| M.get_name (| globals, "env" |), "gas_price" |)
      |) in
    let priority_fee_per_gas :=
      BinOp.sub (|
        M.get_field (| M.get_name (| globals, "env" |), "gas_price" |),
        M.get_field (| M.get_name (| globals, "env" |), "base_fee_per_gas" |)
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
        M.get_name (| globals, "priority_fee_per_gas" |)
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
    let _ :=
      M.for_ (|
        M.get_name (| globals, "address" |),
        M.get_field (| M.get_name (| globals, "output" |), "accounts_to_delete" |),
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
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, "address" |),
        M.get_field (| M.get_name (| globals, "output" |), "touched_accounts" |),
        ltac:(M.monadic (
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
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
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
    let _ :=
      M.for_ (|
        M.get_name (| globals, "byte" |),
        M.get_field (| M.get_name (| globals, "tx" |), "data" |),
        ltac:(M.monadic (
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
    let access_list_cost :=
      Constant.int 0 in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, "isinstance" |),
          make_list [
            M.get_name (| globals, "tx" |);
            make_tuple [ M.get_name (| globals, "AccessListTransaction" |); M.get_name (| globals, "FeeMarketTransaction" |) ]
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          M.for_ (|
            make_tuple [ M.get_name (| globals, "_address" |); M.get_name (| globals, "keys" |) ],
            M.get_field (| M.get_name (| globals, "tx" |), "access_list" |),
            ltac:(M.monadic (
              let access_list_cost := BinOp.add
                M.get_name (| globals, "TX_ACCESS_LIST_ADDRESS_COST" |)
                M.get_name (| globals, "TX_ACCESS_LIST_ADDRESS_COST" |) in
              let access_list_cost := BinOp.add
                BinOp.mult (|
    M.call (|
      M.get_name (| globals, "len" |),
      make_list [
        M.get_name (| globals, "keys" |)
      ],
      make_dict []
    |),
    M.get_name (| globals, "TX_ACCESS_LIST_STORAGE_KEY_COST" |)
  |)
                BinOp.mult (|
    M.call (|
      M.get_name (| globals, "len" |),
      make_list [
        M.get_name (| globals, "keys" |)
      ],
      make_dict []
    |),
    M.get_name (| globals, "TX_ACCESS_LIST_STORAGE_KEY_COST" |)
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
        M.get_name (| globals, "Uint" |),
        make_list [
          BinOp.add (|
            BinOp.add (|
              BinOp.add (|
                M.get_name (| globals, "TX_BASE_COST" |),
                M.get_name (| globals, "data_cost" |)
              |),
              M.get_name (| globals, "create_cost" |)
            |),
            M.get_name (| globals, "access_list_cost" |)
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
      make_tuple [ M.get_name (| globals, "r" |); M.get_name (| globals, "s" |) ],
      make_tuple [ M.get_field (| M.get_name (| globals, "tx" |), "r" |); M.get_field (| M.get_name (| globals, "tx" |), "s" |) ]
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
        let v :=
          M.get_field (| M.get_name (| globals, "tx" |), "v" |) in
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
            let public_key :=
              M.call (|
                M.get_name (| globals, "secp256k1_recover" |),
                make_list [
                  M.get_name (| globals, "r" |);
                  M.get_name (| globals, "s" |);
                  M.get_field (| M.get_name (| globals, "tx" |), "y_parity" |);
                  M.call (|
                    M.get_name (| globals, "signing_hash_2930" |),
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
                let public_key :=
                  M.call (|
                    M.get_name (| globals, "secp256k1_recover" |),
                    make_list [
                      M.get_name (| globals, "r" |);
                      M.get_name (| globals, "s" |);
                      M.get_field (| M.get_name (| globals, "tx" |), "y_parity" |);
                      M.call (|
                        M.get_name (| globals, "signing_hash_1559" |),
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
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Address" |),
        make_list [
          M.slice (|
            M.call (|
              M.get_name (| globals, "keccak256" |),
              make_list [
                M.get_name (| globals, "public_key" |)
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

Definition signing_hash_2930 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx" ] |) in
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
        M.get_name (| globals, "keccak256" |),
        make_list [
          BinOp.add (|
            Constant.bytes "01",
            M.call (|
              M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
              make_list [
                make_tuple [ M.get_field (| M.get_name (| globals, "tx" |), "chain_id" |); M.get_field (| M.get_name (| globals, "tx" |), "nonce" |); M.get_field (| M.get_name (| globals, "tx" |), "gas_price" |); M.get_field (| M.get_name (| globals, "tx" |), "gas" |); M.get_field (| M.get_name (| globals, "tx" |), "to" |); M.get_field (| M.get_name (| globals, "tx" |), "value" |); M.get_field (| M.get_name (| globals, "tx" |), "data" |); M.get_field (| M.get_name (| globals, "tx" |), "access_list" |) ]
              ],
              make_dict []
            |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition signing_hash_1559 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "tx" ] |) in
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
        M.get_name (| globals, "keccak256" |),
        make_list [
          BinOp.add (|
            Constant.bytes "02",
            M.call (|
              M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
              make_list [
                make_tuple [ M.get_field (| M.get_name (| globals, "tx" |), "chain_id" |); M.get_field (| M.get_name (| globals, "tx" |), "nonce" |); M.get_field (| M.get_name (| globals, "tx" |), "max_priority_fee_per_gas" |); M.get_field (| M.get_name (| globals, "tx" |), "max_fee_per_gas" |); M.get_field (| M.get_name (| globals, "tx" |), "gas" |); M.get_field (| M.get_name (| globals, "tx" |), "to" |); M.get_field (| M.get_name (| globals, "tx" |), "value" |); M.get_field (| M.get_name (| globals, "tx" |), "data" |); M.get_field (| M.get_name (| globals, "tx" |), "access_list" |) ]
              ],
              make_dict []
            |)
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
