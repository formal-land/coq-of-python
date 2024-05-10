Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Logs Bloom
^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

This modules defines functions for calculating bloom filters of logs. For the
general theory of bloom filters see e.g. `Wikipedia
<https://en.wikipedia.org/wiki/Bloom_filter>`_. Bloom filters are used to allow
for efficient searching of logs by address and/or topic, by rapidly
eliminating blocks and receipts from their search.
".

Require typing.
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".

Require ethereum.base_types.
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_keccak256 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak256".

Require ethereum.muir_glacier.blocks.
Axiom ethereum_muir_glacier_blocks_Log :
  IsGlobalAlias globals ethereum.muir_glacier.blocks.globals "Log".

Require ethereum.muir_glacier.fork_types.
Axiom ethereum_muir_glacier_fork_types_Bloom :
  IsGlobalAlias globals ethereum.muir_glacier.fork_types.globals "Bloom".

Definition add_to_bloom : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "bloom"; "bloom_entry" ] |) in
    let _ := Constant.str "
    Add a bloom entry to the bloom filter (`bloom`).

    The number of hash functions used is 3. They are calculated by taking the
    least significant 11 bits from the first 3 16-bit words of the
    `keccak_256()` hash of `bloom_entry`.

    Parameters
    ----------
    bloom :
        The bloom filter.
    bloom_entry :
        An entry which is to be added to bloom filter.
    " in
    let hash :=
      M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          M.get_name (| globals, "bloom_entry" |)
        ],
        make_dict []
      |) in
    For M.get_name (| globals, "idx" |) in make_tuple [ Constant.int 0; Constant.int 2; Constant.int 4 ] do
      let bit_to_set :=
        BinOp.bit_and (|
          M.call (|
            M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
            make_list [
              M.get_subscript (| M.get_name (| globals, "hash" |), M.slice (| M.get_name (| globals, "idx" |), BinOp.add (|
                M.get_name (| globals, "idx" |),
                Constant.int 2
              |) |) |)
            ],
            make_dict []
          |),
          Constant.int 2047
        |) in
      let bit_index :=
        BinOp.sub (|
          Constant.int 2047,
          M.get_name (| globals, "bit_to_set" |)
        |) in
      let byte_index :=
        BinOp.floor_div (|
          M.get_name (| globals, "bit_index" |),
          Constant.int 8
        |) in
      let bit_value :=
        BinOp.l_shift (|
          Constant.int 1,
          BinOp.sub (|
            Constant.int 7,
            BinOp.mod_ (|
              M.get_name (| globals, "bit_index" |),
              Constant.int 8
            |)
          |)
        |) in
      let _ := M.assign (|
        M.get_subscript (| M.get_name (| globals, "bloom" |), M.get_name (| globals, "byte_index" |) |),
        BinOp.bit_or (|
          M.get_subscript (| M.get_name (| globals, "bloom" |), M.get_name (| globals, "byte_index" |) |),
          M.get_name (| globals, "bit_value" |)
        |)
      |) in
    EndFor.
    M.pure Constant.None_)).

Definition logs_bloom : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "logs" ] |) in
    let _ := Constant.str "
    Obtain the logs bloom from a list of log entries.

    The address and each topic of a log are added to the bloom filter.

    Parameters
    ----------
    logs :
        List of logs for which the logs bloom is to be obtained.

    Returns
    -------
    logs_bloom : `Bloom`
        The logs bloom obtained which is 256 bytes with some bits set as per
        the caller address and the log topics.
    " in
(* At stmt: unsupported node type: AnnAssign *)
    For M.get_name (| globals, "log" |) in M.get_name (| globals, "logs" |) do
      let _ := M.call (|
    M.get_name (| globals, "add_to_bloom" |),
    make_list [
      M.get_name (| globals, "bloom" |);
      M.get_field (| M.get_name (| globals, "log" |), "address" |)
    ],
    make_dict []
  |) in
      For M.get_name (| globals, "topic" |) in M.get_field (| M.get_name (| globals, "log" |), "topics" |) do
        let _ := M.call (|
    M.get_name (| globals, "add_to_bloom" |),
    make_list [
      M.get_name (| globals, "bloom" |);
      M.get_name (| globals, "topic" |)
    ],
    make_dict []
  |) in
      EndFor.
    EndFor.
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Bloom" |),
        make_list [
          M.get_name (| globals, "bloom" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
