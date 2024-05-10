Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.london.bloom".

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

Axiom typing_imports :
  AreImported globals "typing" [ "Tuple" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "Uint" ].

Axiom ethereum_crypto_hash_imports :
  AreImported globals "ethereum.crypto.hash" [ "keccak256" ].

Axiom ethereum_london_blocks_imports :
  AreImported globals "ethereum.london.blocks" [ "Log" ].

Axiom ethereum_london_fork_types_imports :
  AreImported globals "ethereum.london.fork_types" [ "Bloom" ].

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
    let _ :=
      M.for_ (|
        M.get_name (| globals, "idx" |),
        make_tuple [ Constant.int 0; Constant.int 2; Constant.int 4 ],
        ltac:(M.monadic (
          let bit_to_set :=
            BinOp.bit_and (|
              M.call (|
                M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
                make_list [
                  M.slice (|
                    M.get_name (| globals, "hash" |),
                    M.get_name (| globals, "idx" |),
                    BinOp.add (|
                      M.get_name (| globals, "idx" |),
                      Constant.int 2
                    |),
                    Constant.None_
                  |)
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
            M.get_subscript (|
              M.get_name (| globals, "bloom" |),
              M.get_name (| globals, "byte_index" |)
            |),
            BinOp.bit_or (|
              M.get_subscript (|
                M.get_name (| globals, "bloom" |),
                M.get_name (| globals, "byte_index" |)
              |),
              M.get_name (| globals, "bit_value" |)
            |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
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
    let _ :=
      M.for_ (|
        M.get_name (| globals, "log" |),
        M.get_name (| globals, "logs" |),
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_name (| globals, "add_to_bloom" |),
    make_list [
      M.get_name (| globals, "bloom" |);
      M.get_field (| M.get_name (| globals, "log" |), "address" |)
    ],
    make_dict []
  |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, "topic" |),
              M.get_field (| M.get_name (| globals, "log" |), "topics" |),
              ltac:(M.monadic (
                let _ := M.call (|
    M.get_name (| globals, "add_to_bloom" |),
    make_list [
      M.get_name (| globals, "bloom" |);
      M.get_name (| globals, "topic" |)
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
