Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethash is a proof-of-work algorithm designed to be [ASIC] resistant through
[memory hardness][mem-hard].

To achieve memory hardness, computing Ethash requires access to subsets of a
large structure. The particular subsets chosen are based on the nonce and block
header, while the set itself is changed every [`epoch`].

At a high level, the Ethash algorithm is as follows:

1. Create a **seed** value, generated with [`generate_seed`] and based on the
   preceding block numbers.
1. From the seed, compute a pseudorandom **cache** with [`generate_cache`].
1. From the cache, generate a **dataset** with [`generate_dataset`]. The
   dataset grows over time based on [`DATASET_EPOCH_GROWTH_SIZE`].
1. Miners hash slices of the dataset together, which is where the memory
   hardness is introduced. Verification of the proof-of-work only requires the
   cache to be able to recompute a much smaller subset of the full dataset.

[`DATASET_EPOCH_GROWTH_SIZE`]: ref:ethereum.ethash.DATASET_EPOCH_GROWTH_SIZE
[`generate_dataset`]: ref:ethereum.ethash.generate_dataset
[`generate_cache`]: ref:ethereum.ethash.generate_cache
[`generate_seed`]: ref:ethereum.ethash.generate_seed
[`epoch`]: ref:ethereum.ethash.epoch
[ASIC]: https://en.wikipedia.org/wiki/Application-specific_integrated_circuit
[mem-hard]: https://en.wikipedia.org/wiki/Memory-hard_function
".

Require typing.
Axiom typing_Callable :
  IsGlobalAlias globals typing.globals "Callable".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".

Require ethereum.base_types.
Axiom ethereum_base_types_U32 :
  IsGlobalAlias globals ethereum.base_types.globals "U32".
Axiom ethereum_base_types_Bytes8 :
  IsGlobalAlias globals ethereum.base_types.globals "Bytes8".
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_Hash32 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "Hash32".
Axiom ethereum_crypto_hash_Hash64 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "Hash64".
Axiom ethereum_crypto_hash_keccak256 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak256".
Axiom ethereum_crypto_hash_keccak512 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak512".

Require ethereum.utils.numeric.
Axiom ethereum_utils_numeric_is_prime :
  IsGlobalAlias globals ethereum.utils.numeric.globals "is_prime".
Axiom ethereum_utils_numeric_le_bytes_to_uint32_sequence :
  IsGlobalAlias globals ethereum.utils.numeric.globals "le_bytes_to_uint32_sequence".
Axiom ethereum_utils_numeric_le_uint32_sequence_to_bytes :
  IsGlobalAlias globals ethereum.utils.numeric.globals "le_uint32_sequence_to_bytes".
Axiom ethereum_utils_numeric_le_uint32_sequence_to_uint :
  IsGlobalAlias globals ethereum.utils.numeric.globals "le_uint32_sequence_to_uint".

Definition EPOCH_SIZE : Value.t := M.run ltac:(M.monadic (
  Constant.int 30000
)).

Definition expr_41 : Value.t :=
  Constant.str "
Number of blocks before a dataset needs to be regenerated (known as an
"""epoch""".) See [`epoch`].

[`epoch`]: ref:ethereum.ethash.epoch
".

Definition INITIAL_CACHE_SIZE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (|
    Constant.int 2,
    Constant.int 24
  |)
)).

Definition expr_49 : Value.t :=
  Constant.str "
Size of the cache (in bytes) during the first epoch. Each subsequent epoch's
cache roughly grows by [`CACHE_EPOCH_GROWTH_SIZE`] bytes. See [`cache_size`].

[`CACHE_EPOCH_GROWTH_SIZE`]: ref:ethereum.ethash.CACHE_EPOCH_GROWTH_SIZE
[`cache_size`]: ref:ethereum.ethash.cache_size
".

Definition CACHE_EPOCH_GROWTH_SIZE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (|
    Constant.int 2,
    Constant.int 17
  |)
)).

Definition expr_58 : Value.t :=
  Constant.str "
After the first epoch, the cache size grows by roughly this amount. See
[`cache_size`].

[`cache_size`]: ref:ethereum.ethash.cache_size
".

Definition INITIAL_DATASET_SIZE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (|
    Constant.int 2,
    Constant.int 30
  |)
)).

Definition expr_66 : Value.t :=
  Constant.str "
Size of the dataset (in bytes) during the first epoch. Each subsequent epoch's
dataset roughly grows by [`DATASET_EPOCH_GROWTH_SIZE`] bytes. See
[`dataset_size`].

[`DATASET_EPOCH_GROWTH_SIZE`]: ref:ethereum.ethash.DATASET_EPOCH_GROWTH_SIZE
[`dataset_size`]: ref:ethereum.ethash.dataset_size
".

Definition DATASET_EPOCH_GROWTH_SIZE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (|
    Constant.int 2,
    Constant.int 23
  |)
)).

Definition expr_76 : Value.t :=
  Constant.str "
After the first epoch, the dataset size grows by roughly this amount. See
[`dataset_size`].

[`dataset_size`]: ref:ethereum.ethash.dataset_size
".

Definition HASH_BYTES : Value.t := M.run ltac:(M.monadic (
  Constant.int 64
)).

Definition expr_84 : Value.t :=
  Constant.str "
Length of a hash, in bytes.
".

Definition MIX_BYTES : Value.t := M.run ltac:(M.monadic (
  Constant.int 128
)).

Definition expr_89 : Value.t :=
  Constant.str "
Width of mix, in bytes. See [`generate_dataset_item`].

[`generate_dataset_item`]: ref:ethereum.ethash.generate_dataset_item
".

Definition CACHE_ROUNDS : Value.t := M.run ltac:(M.monadic (
  Constant.int 3
)).

Definition expr_96 : Value.t :=
  Constant.str "
Number of times to repeat the [`keccak512`] step while generating the hash. See
[`generate_cache`].

[`keccak512`]: ref:ethereum.crypto.hash.keccak512
[`generate_cache`]: ref:ethereum.ethash.generate_cache
".

Definition DATASET_PARENTS : Value.t := M.run ltac:(M.monadic (
  Constant.int 256
)).

Definition expr_105 : Value.t :=
  Constant.str "
Number of parents of each dataset element. See [`generate_dataset_item`].

[`generate_dataset_item`]: ref:ethereum.ethash.generate_dataset_item
".

Definition HASHIMOTO_ACCESSES : Value.t := M.run ltac:(M.monadic (
  Constant.int 64
)).

Definition expr_112 : Value.t :=
  Constant.str "
Number of accesses in the [`hashimoto`] loop.

[`hashimoto`]: ref:ethereum.ethash.hashimoto
".

Definition epoch : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "block_number" ] |) in
    let _ := Constant.str "
    Obtain the epoch number to which the block identified by `block_number`
    belongs. The first epoch is numbered zero.

    An Ethash epoch is a fixed number of blocks ([`EPOCH_SIZE`]) long, during
    which the dataset remains constant. At the end of each epoch, the dataset
    is generated anew. See [`generate_dataset`].

    [`EPOCH_SIZE`]: ref:ethereum.ethash.EPOCH_SIZE
    [`generate_dataset`]: ref:ethereum.ethash.generate_dataset
    " in
    let _ := M.return_ (|
      BinOp.floor_div (|
        M.get_name (| globals, "block_number" |),
        M.get_name (| globals, "EPOCH_SIZE" |)
      |)
    |) in
    M.pure Constant.None_)).

Definition cache_size : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "block_number" ] |) in
    let _ := Constant.str "
    Obtain the cache size (in bytes) of the epoch to which `block_number`
    belongs.

    See [`INITIAL_CACHE_SIZE`] and [`CACHE_EPOCH_GROWTH_SIZE`] for the initial
    size and linear growth rate, respectively. The cache is generated in
    [`generate_cache`].

    The actual cache size is smaller than simply multiplying
    `CACHE_EPOCH_GROWTH_SIZE` by the epoch number to minimize the risk of
    unintended cyclic behavior. It is defined as the highest prime number below
    what linear growth would calculate.

    [`INITIAL_CACHE_SIZE`]: ref:ethereum.ethash.INITIAL_CACHE_SIZE
    [`CACHE_EPOCH_GROWTH_SIZE`]: ref:ethereum.ethash.CACHE_EPOCH_GROWTH_SIZE
    [`generate_cache`]: ref:ethereum.ethash.generate_cache
    " in
    let size :=
      BinOp.add (|
        M.get_name (| globals, "INITIAL_CACHE_SIZE" |),
        BinOp.mult (|
          M.get_name (| globals, "CACHE_EPOCH_GROWTH_SIZE" |),
          M.call (|
            M.get_name (| globals, "epoch" |),
            make_list [
              M.get_name (| globals, "block_number" |)
            ],
            make_dict []
          |)
        |)
      |) in
    let size := BinOp.sub
      M.get_name (| globals, "HASH_BYTES" |)
      M.get_name (| globals, "HASH_BYTES" |) in
    While UnOp.not (| M.call (|
    M.get_name (| globals, "is_prime" |),
    make_list [
      BinOp.floor_div (|
        M.get_name (| globals, "size" |),
        M.get_name (| globals, "HASH_BYTES" |)
      |)
    ],
    make_dict []
  |) |) do
      let size := BinOp.sub
        BinOp.mult (|
    Constant.int 2,
    M.get_name (| globals, "HASH_BYTES" |)
  |)
        BinOp.mult (|
    Constant.int 2,
    M.get_name (| globals, "HASH_BYTES" |)
  |) in
    EndWhile.
    let _ := M.return_ (|
      M.get_name (| globals, "size" |)
    |) in
    M.pure Constant.None_)).

Definition dataset_size : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "block_number" ] |) in
    let _ := Constant.str "
    Obtain the dataset size (in bytes) of the epoch to which `block_number`
    belongs.

    See [`INITIAL_DATASET_SIZE`] and [`DATASET_EPOCH_GROWTH_SIZE`][ds] for the
    initial size and linear growth rate, respectively. The complete dataset is
    generated in [`generate_dataset`], while the slices used in verification
    are generated in [`generate_dataset_item`].

    The actual dataset size is smaller than simply multiplying
    `DATASET_EPOCH_GROWTH_SIZE` by the epoch number to minimize the risk of
    unintended cyclic behavior. It is defined as the highest prime number below
    what linear growth would calculate.

    [`INITIAL_DATASET_SIZE`]: ref:ethereum.ethash.INITIAL_DATASET_SIZE
    [ds]: ref:ethereum.ethash.DATASET_EPOCH_GROWTH_SIZE
    [`generate_dataset`]: ref:ethereum.ethash.generate_dataset
    [`generate_dataset_item`]: ref:ethereum.ethash.generate_dataset_item
    " in
    let size :=
      BinOp.add (|
        M.get_name (| globals, "INITIAL_DATASET_SIZE" |),
        BinOp.mult (|
          M.get_name (| globals, "DATASET_EPOCH_GROWTH_SIZE" |),
          M.call (|
            M.get_name (| globals, "epoch" |),
            make_list [
              M.get_name (| globals, "block_number" |)
            ],
            make_dict []
          |)
        |)
      |) in
    let size := BinOp.sub
      M.get_name (| globals, "MIX_BYTES" |)
      M.get_name (| globals, "MIX_BYTES" |) in
    While UnOp.not (| M.call (|
    M.get_name (| globals, "is_prime" |),
    make_list [
      BinOp.floor_div (|
        M.get_name (| globals, "size" |),
        M.get_name (| globals, "MIX_BYTES" |)
      |)
    ],
    make_dict []
  |) |) do
      let size := BinOp.sub
        BinOp.mult (|
    Constant.int 2,
    M.get_name (| globals, "MIX_BYTES" |)
  |)
        BinOp.mult (|
    Constant.int 2,
    M.get_name (| globals, "MIX_BYTES" |)
  |) in
    EndWhile.
    let _ := M.return_ (|
      M.get_name (| globals, "size" |)
    |) in
    M.pure Constant.None_)).

Definition generate_seed : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "block_number" ] |) in
    let _ := Constant.str "
    Obtain the cache generation seed for the block identified by
    `block_number`. See [`generate_cache`].

    [`generate_cache`]: ref:ethereum.ethash.generate_cache
    " in
    let epoch_number :=
      M.call (|
        M.get_name (| globals, "epoch" |),
        make_list [
          M.get_name (| globals, "block_number" |)
        ],
        make_dict []
      |) in
    let seed :=
      BinOp.mult (|
        (* At constant: unsupported node type: Constant *),
        Constant.int 32
      |) in
    While Compare.not_eq (| M.get_name (| globals, "epoch_number" |), Constant.int 0 |) do
      let seed :=
        M.call (|
          M.get_name (| globals, "keccak256" |),
          make_list [
            M.get_name (| globals, "seed" |)
          ],
          make_dict []
        |) in
      let epoch_number := BinOp.sub
        Constant.int 1
        Constant.int 1 in
    EndWhile.
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Hash32" |),
        make_list [
          M.get_name (| globals, "seed" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition generate_cache : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "block_number" ] |) in
    let _ := Constant.str "
    Generate the cache for the block identified by `block_number`. See
    [`generate_dataset`] for how the cache is used.

    The cache is generated in two steps: filling the array with a chain of
    [`keccak512`] hashes, then running two rounds of Sergio Demian Lerner's
    [RandMemoHash] on those bytes.

    [`keccak512`]: ref:ethereum.crypto.hash.keccak512
    [`generate_dataset`]: ref:ethereum.ethash.generate_dataset
    [RandMemoHash]: http://www.hashcash.org/papers/memohash.pdf
    " in
    let seed :=
      M.call (|
        M.get_name (| globals, "generate_seed" |),
        make_list [
          M.get_name (| globals, "block_number" |)
        ],
        make_dict []
      |) in
    let cache_size_bytes :=
      M.call (|
        M.get_name (| globals, "cache_size" |),
        make_list [
          M.get_name (| globals, "block_number" |)
        ],
        make_dict []
      |) in
    let cache_size_words :=
      BinOp.floor_div (|
        M.get_name (| globals, "cache_size_bytes" |),
        M.get_name (| globals, "HASH_BYTES" |)
      |) in
    let cache :=
      make_list [
        M.call (|
          M.get_name (| globals, "keccak512" |),
          make_list [
            M.get_name (| globals, "seed" |)
          ],
          make_dict []
        |)
      ] in
    For M.get_name (| globals, "index" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      Constant.int 1;
      M.get_name (| globals, "cache_size_words" |)
    ],
    make_dict []
  |) do
      let cache_item :=
        M.call (|
          M.get_name (| globals, "keccak512" |),
          make_list [
            M.get_subscript (| M.get_name (| globals, "cache" |), BinOp.sub (|
              M.get_name (| globals, "index" |),
              Constant.int 1
            |) |)
          ],
          make_dict []
        |) in
      let _ := M.call (|
    M.get_field (| M.get_name (| globals, "cache" |), "append" |),
    make_list [
      M.get_name (| globals, "cache_item" |)
    ],
    make_dict []
  |) in
    EndFor.
    For M.get_name (| globals, "_" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      M.get_name (| globals, "CACHE_ROUNDS" |)
    ],
    make_dict []
  |) do
      For M.get_name (| globals, "index" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      M.get_name (| globals, "cache_size_words" |)
    ],
    make_dict []
  |) do
        let first_cache_item :=
          M.get_subscript (| M.get_name (| globals, "cache" |), BinOp.mod_ (|
            BinOp.add (|
              BinOp.sub (|
                M.get_name (| globals, "index" |),
                Constant.int 1
              |),
              M.call (|
                M.get_name (| globals, "int" |),
                make_list [
                  M.get_name (| globals, "cache_size_words" |)
                ],
                make_dict []
              |)
            |),
            M.get_name (| globals, "cache_size_words" |)
          |) |) in
        let second_cache_item :=
          M.get_subscript (| M.get_name (| globals, "cache" |), BinOp.mod_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "U32" |), "from_le_bytes" |),
              make_list [
                M.get_subscript (| M.get_subscript (| M.get_name (| globals, "cache" |), M.get_name (| globals, "index" |) |), Constant.int 0:Constant.int 4 |)
              ],
              make_dict []
            |),
            M.get_name (| globals, "cache_size_words" |)
          |) |) in
        let result :=
          M.call (|
            M.get_name (| globals, "bytes" |),
            make_list [
              [BinOp.bit_xor (|
                M.get_name (| globals, "a" |),
                M.get_name (| globals, "b" |)
              |) for (* At expr: unsupported node type: list *)]
            ],
            make_dict []
          |) in
        let _ := M.assign (|
          M.get_subscript (| M.get_name (| globals, "cache" |), M.get_name (| globals, "index" |) |),
          M.call (|
            M.get_name (| globals, "keccak512" |),
            make_list [
              M.get_name (| globals, "result" |)
            ],
            make_dict []
          |)
        |) in
      EndFor.
    EndFor.
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "tuple" |),
        make_list [
          (M.call (|
            M.get_name (| globals, "le_bytes_to_uint32_sequence" |),
            make_list [
              M.get_name (| globals, "cache_item" |)
            ],
            make_dict []
          |) for (* At expr: unsupported node type: list *))
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition fnv : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "a"; "b" ] |) in
    let _ := Constant.str "
    A non-associative substitute for XOR, inspired by the [FNV] hash by Fowler,
    Noll, and Vo. See [`fnv_hash`], [`generate_dataset_item`], and
    [`hashimoto`].

    Note that here we multiply the prime with the full 32-bit input, in
    contrast with the [FNV-1] spec which multiplies the prime with one byte
    (octet) in turn.

    [`hashimoto`]: ref:ethereum.ethash.hashimoto
    [`generate_dataset_item`]: ref:ethereum.ethash.generate_dataset_item
    [`fnv_hash`]: ref:ethereum.ethash.fnv_hash
    [FNV]: https://w.wiki/XKZ
    [FNV-1]: http://www.isthe.com/chongo/tech/comp/fnv/#FNV-1
    " in
    let result :=
      BinOp.bit_and (|
        BinOp.bit_xor (|
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, "Uint" |),
              make_list [
                M.get_name (| globals, "a" |)
              ],
              make_dict []
            |),
            Constant.int 16777619
          |),
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "b" |)
            ],
            make_dict []
          |)
        |),
        M.get_field (| M.get_name (| globals, "U32" |), "MAX_VALUE" |)
      |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "U32" |),
        make_list [
          M.get_name (| globals, "result" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition fnv_hash : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "mix_integers"; "data" ] |) in
    let _ := Constant.str "
    Combines `data` into `mix_integers` using [`fnv`]. See [`hashimoto`] and
    [`generate_dataset_item`].

    [`hashimoto`]: ref:ethereum.ethash.hashimoto
    [`generate_dataset_item`]: ref:ethereum.ethash.generate_dataset_item
    [`fnv`]: ref:ethereum.ethash.fnv
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "tuple" |),
        make_list [
          (M.call (|
            M.get_name (| globals, "fnv" |),
            make_list [
              M.get_subscript (| M.get_name (| globals, "mix_integers" |), M.get_name (| globals, "i" |) |);
              M.get_subscript (| M.get_name (| globals, "data" |), M.get_name (| globals, "i" |) |)
            ],
            make_dict []
          |) for (* At expr: unsupported node type: list *))
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition generate_dataset_item : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "cache"; "index" ] |) in
    let _ := Constant.str "
    Generate a particular dataset item 0-indexed by `index` by hashing
    pseudorandomly-selected entries from `cache` together. See [`fnv`] and
    [`fnv_hash`] for the digest function, [`generate_cache`] for generating
    `cache`, and [`generate_dataset`] for the full dataset generation
    algorithm.

    [`fnv`]: ref:ethereum.ethash.fnv
    [`fnv_hash`]: ref:ethereum.ethash.fnv_hash
    [`generate_dataset`]: ref:ethereum.ethash.generate_dataset
    [`generate_cache`]: ref:ethereum.ethash.generate_cache
    " in
    let mix :=
      M.call (|
        M.get_name (| globals, "keccak512" |),
        make_list [
          M.call (|
            M.get_field (| BinOp.bit_xor (|
              M.call (|
                M.get_name (| globals, "le_uint32_sequence_to_uint" |),
                make_list [
                  M.get_subscript (| M.get_name (| globals, "cache" |), BinOp.mod_ (|
                    M.get_name (| globals, "index" |),
                    M.call (|
                      M.get_name (| globals, "len" |),
                      make_list [
                        M.get_name (| globals, "cache" |)
                      ],
                      make_dict []
                    |)
                  |) |)
                ],
                make_dict []
              |),
              M.get_name (| globals, "index" |)
            |), "to_le_bytes" |),
            make_list [],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let mix_integers :=
      M.call (|
        M.get_name (| globals, "le_bytes_to_uint32_sequence" |),
        make_list [
          M.get_name (| globals, "mix" |)
        ],
        make_dict []
      |) in
    For M.get_name (| globals, "j" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      M.get_name (| globals, "DATASET_PARENTS" |)
    ],
    make_dict []
  |) do
(* At stmt: unsupported node type: AnnAssign *)
      let cache_index :=
        BinOp.mod_ (|
          M.call (|
            M.get_name (| globals, "fnv" |),
            make_list [
              BinOp.bit_xor (|
                M.get_name (| globals, "index" |),
                M.get_name (| globals, "j" |)
              |);
              M.get_name (| globals, "mix_word" |)
            ],
            make_dict []
          |),
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_name (| globals, "cache" |)
            ],
            make_dict []
          |)
        |) in
      let parent :=
        M.get_subscript (| M.get_name (| globals, "cache" |), M.get_name (| globals, "cache_index" |) |) in
      let mix_integers :=
        M.call (|
          M.get_name (| globals, "fnv_hash" |),
          make_list [
            M.get_name (| globals, "mix_integers" |);
            M.get_name (| globals, "parent" |)
          ],
          make_dict []
        |) in
    EndFor.
    let mix :=
      M.call (|
        M.get_name (| globals, "Hash64" |),
        make_list [
          M.call (|
            M.get_name (| globals, "le_uint32_sequence_to_bytes" |),
            make_list [
              M.get_name (| globals, "mix_integers" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "keccak512" |),
        make_list [
          M.get_name (| globals, "mix" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition generate_dataset : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "block_number" ] |) in
    let _ := Constant.str "
    Generate the full dataset for the block identified by `block_number`.

    This function is present only for demonstration purposes. It is not used
    while validating blocks.
    " in
(* At stmt: unsupported node type: AnnAssign *)
(* At stmt: unsupported node type: AnnAssign *)
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "tuple" |),
        make_list [
          (M.call (|
            M.get_name (| globals, "generate_dataset_item" |),
            make_list [
              M.get_name (| globals, "cache" |);
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  M.get_name (| globals, "index" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |) for (* At expr: unsupported node type: list *))
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition hashimoto : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "header_hash"; "nonce"; "dataset_size"; "fetch_dataset_item" ] |) in
    let _ := Constant.str "
    Obtain the mix digest and the final value for a header, by aggregating
    data from the full dataset.

    #### Parameters

    - `header_hash` is a valid [RLP hash] of a block header.
    - `nonce` is the propagated nonce for the given block.
    - `dataset_size` is the size of the dataset. See [`dataset_size`].
    - `fetch_dataset_item` is a function that retrieves a specific dataset item
      based on its index.

    #### Returns

    - The mix digest generated from the header hash and propagated nonce.
    - The final result obtained which will be checked for leading zeros (in
      byte representation) in correspondence with the block difficulty.

    [RLP hash]: ref:ethereum.rlp.rlp_hash
    [`dataset_size`]: ref:ethereum.ethash.dataset_size
    " in
    let nonce_le :=
      M.call (|
        M.get_name (| globals, "bytes" |),
        make_list [
          M.call (|
            M.get_name (| globals, "reversed" |),
            make_list [
              M.get_name (| globals, "nonce" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let seed_hash :=
      M.call (|
        M.get_name (| globals, "keccak512" |),
        make_list [
          BinOp.add (|
            M.get_name (| globals, "header_hash" |),
            M.get_name (| globals, "nonce_le" |)
          |)
        ],
        make_dict []
      |) in
    let seed_head :=
      M.call (|
        M.get_field (| M.get_name (| globals, "U32" |), "from_le_bytes" |),
        make_list [
          M.get_subscript (| M.get_name (| globals, "seed_hash" |), (* At expr: unsupported node type: NoneType *):Constant.int 4 |)
        ],
        make_dict []
      |) in
    let rows :=
      BinOp.floor_div (|
        M.get_name (| globals, "dataset_size" |),
        Constant.int 128
      |) in
    let mix :=
      BinOp.mult (|
        M.call (|
          M.get_name (| globals, "le_bytes_to_uint32_sequence" |),
          make_list [
            M.get_name (| globals, "seed_hash" |)
          ],
          make_dict []
        |),
        BinOp.floor_div (|
          M.get_name (| globals, "MIX_BYTES" |),
          M.get_name (| globals, "HASH_BYTES" |)
        |)
      |) in
    For M.get_name (| globals, "i" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      M.get_name (| globals, "HASHIMOTO_ACCESSES" |)
    ],
    make_dict []
  |) do
(* At stmt: unsupported node type: AnnAssign *)
      let parent :=
        BinOp.mod_ (|
          M.call (|
            M.get_name (| globals, "fnv" |),
            make_list [
              BinOp.bit_xor (|
                M.get_name (| globals, "i" |),
                M.get_name (| globals, "seed_head" |)
              |);
              M.get_subscript (| M.get_name (| globals, "mix" |), BinOp.mod_ (|
                M.get_name (| globals, "i" |),
                M.call (|
                  M.get_name (| globals, "len" |),
                  make_list [
                    M.get_name (| globals, "mix" |)
                  ],
                  make_dict []
                |)
              |) |)
            ],
            make_dict []
          |),
          M.get_name (| globals, "rows" |)
        |) in
      For M.get_name (| globals, "j" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      BinOp.floor_div (|
        M.get_name (| globals, "MIX_BYTES" |),
        M.get_name (| globals, "HASH_BYTES" |)
      |)
    ],
    make_dict []
  |) do
        let new_data := BinOp.add
          M.call (|
    M.get_name (| globals, "fetch_dataset_item" |),
    make_list [
      BinOp.add (|
        BinOp.mult (|
          Constant.int 2,
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "parent" |)
            ],
            make_dict []
          |)
        |),
        M.get_name (| globals, "j" |)
      |)
    ],
    make_dict []
  |)
          M.call (|
    M.get_name (| globals, "fetch_dataset_item" |),
    make_list [
      BinOp.add (|
        BinOp.mult (|
          Constant.int 2,
          M.call (|
            M.get_name (| globals, "Uint" |),
            make_list [
              M.get_name (| globals, "parent" |)
            ],
            make_dict []
          |)
        |),
        M.get_name (| globals, "j" |)
      |)
    ],
    make_dict []
  |) in
      EndFor.
      let mix :=
        M.call (|
          M.get_name (| globals, "fnv_hash" |),
          make_list [
            M.get_name (| globals, "mix" |);
            M.get_name (| globals, "new_data" |)
          ],
          make_dict []
        |) in
    EndFor.
    let compressed_mix :=
      make_list [] in
    For M.get_name (| globals, "i" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      Constant.int 0;
      M.call (|
        M.get_name (| globals, "len" |),
        make_list [
          M.get_name (| globals, "mix" |)
        ],
        make_dict []
      |);
      Constant.int 4
    ],
    make_dict []
  |) do
      let _ := M.call (|
    M.get_field (| M.get_name (| globals, "compressed_mix" |), "append" |),
    make_list [
      M.call (|
        M.get_name (| globals, "fnv" |),
        make_list [
          M.call (|
            M.get_name (| globals, "fnv" |),
            make_list [
              M.call (|
                M.get_name (| globals, "fnv" |),
                make_list [
                  M.get_subscript (| M.get_name (| globals, "mix" |), M.get_name (| globals, "i" |) |);
                  M.get_subscript (| M.get_name (| globals, "mix" |), BinOp.add (|
                    M.get_name (| globals, "i" |),
                    Constant.int 1
                  |) |)
                ],
                make_dict []
              |);
              M.get_subscript (| M.get_name (| globals, "mix" |), BinOp.add (|
                M.get_name (| globals, "i" |),
                Constant.int 2
              |) |)
            ],
            make_dict []
          |);
          M.get_subscript (| M.get_name (| globals, "mix" |), BinOp.add (|
            M.get_name (| globals, "i" |),
            Constant.int 3
          |) |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    EndFor.
    let mix_digest :=
      M.call (|
        M.get_name (| globals, "le_uint32_sequence_to_bytes" |),
        make_list [
          M.get_name (| globals, "compressed_mix" |)
        ],
        make_dict []
      |) in
    let result :=
      M.call (|
        M.get_name (| globals, "keccak256" |),
        make_list [
          BinOp.add (|
            M.get_name (| globals, "seed_hash" |),
            M.get_name (| globals, "mix_digest" |)
          |)
        ],
        make_dict []
      |) in
    let _ := M.return_ (|
      make_tuple [ M.get_name (| globals, "mix_digest" |); M.get_name (| globals, "result" |) ]
    |) in
    M.pure Constant.None_)).

Definition hashimoto_light : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "header_hash"; "nonce"; "cache"; "dataset_size" ] |) in
    let _ := Constant.str "
    Run the [`hashimoto`] algorithm by generating dataset item using the cache
    instead of loading the full dataset into main memory.

    #### Parameters

    - `header_hash` is a valid [RLP hash] of a block header.
    - `nonce` is the propagated nonce for the given block.
    - `cache` is the cache generated by [`generate_cache`].
    - `dataset_size` is the size of the dataset. See [`dataset_size`].

    #### Returns

    - The mix digest generated from the header hash and propagated nonce.
    - The final result obtained which will be checked for leading zeros (in
      byte representation) in correspondence with the block difficulty.

    [RLP hash]: ref:ethereum.rlp.rlp_hash
    [`dataset_size`]: ref:ethereum.ethash.dataset_size
    [`generate_cache`]: ref:ethereum.ethash.generate_cache
    [`hashimoto`]: ref:ethereum.ethash.hashimoto
    " in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "hashimoto" |),
        make_list [
          M.get_name (| globals, "header_hash" |);
          M.get_name (| globals, "nonce" |);
          M.get_name (| globals, "dataset_size" |);
          M.get_name (| globals, "fetch_dataset_item" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).