Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
State Trie
^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

The state trie is the structure responsible for storing
`.fork_types.Account` objects.
".

(* At top_level_stmt: unsupported node type: Import *)

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".
Axiom dataclasses_field :
  IsGlobalAlias globals dataclasses.globals "field".

Require typing.
Axiom typing_Callable :
  IsGlobalAlias globals typing.globals "Callable".
Axiom typing_Dict :
  IsGlobalAlias globals typing.globals "Dict".
Axiom typing_Generic :
  IsGlobalAlias globals typing.globals "Generic".
Axiom typing_List :
  IsGlobalAlias globals typing.globals "List".
Axiom typing_Mapping :
  IsGlobalAlias globals typing.globals "Mapping".
Axiom typing_MutableMapping :
  IsGlobalAlias globals typing.globals "MutableMapping".
Axiom typing_Optional :
  IsGlobalAlias globals typing.globals "Optional".
Axiom typing_Sequence :
  IsGlobalAlias globals typing.globals "Sequence".
Axiom typing_TypeVar :
  IsGlobalAlias globals typing.globals "TypeVar".
Axiom typing_Union :
  IsGlobalAlias globals typing.globals "Union".
Axiom typing_cast :
  IsGlobalAlias globals typing.globals "cast".

Require ethereum.crypto.hash.
Axiom ethereum_crypto_hash_keccak256 :
  IsGlobalAlias globals ethereum.crypto.hash.globals "keccak256".

Require ethereum.gray_glacier.
Axiom ethereum_gray_glacier_trie :
  IsGlobalAlias globals ethereum.gray_glacier.globals "trie".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require ethereum.utils.hexadecimal.
Axiom ethereum_utils_hexadecimal_hex_to_bytes :
  IsGlobalAlias globals ethereum.utils.hexadecimal.globals "hex_to_bytes".

Require __init__.
Axiom __init___rlp :
  IsGlobalAlias globals __init__.globals "rlp".

Require base_types.
Axiom base_types_U256 :
  IsGlobalAlias globals base_types.globals "U256".
Axiom base_types_Bytes :
  IsGlobalAlias globals base_types.globals "Bytes".
Axiom base_types_Uint :
  IsGlobalAlias globals base_types.globals "Uint".
Axiom base_types_slotted_freezable :
  IsGlobalAlias globals base_types.globals "slotted_freezable".

Require blocks.
Axiom blocks_Receipt :
  IsGlobalAlias globals blocks.globals "Receipt".

Require fork_types.
Axiom fork_types_Account :
  IsGlobalAlias globals fork_types.globals "Account".
Axiom fork_types_Address :
  IsGlobalAlias globals fork_types.globals "Address".
Axiom fork_types_Root :
  IsGlobalAlias globals fork_types.globals "Root".
Axiom fork_types_encode_account :
  IsGlobalAlias globals fork_types.globals "encode_account".

Require transactions.
Axiom transactions_LegacyTransaction :
  IsGlobalAlias globals transactions.globals "LegacyTransaction".

Definition EMPTY_TRIE_ROOT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "Root" |),
    make_list [
      M.call (|
        M.get_name (| globals, "hex_to_bytes" |),
        make_list [
          Constant.str "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
        ],
        make_dict []
      |)
    ],
    make_dict []
  |)
)).

Definition Node : Value.t := M.run ltac:(M.monadic (
  M.get_subscript (| M.get_name (| globals, "Union" |), make_tuple [ M.get_name (| globals, "Account" |); M.get_name (| globals, "Bytes" |); M.get_name (| globals, "LegacyTransaction" |); M.get_name (| globals, "Receipt" |); M.get_name (| globals, "Uint" |); M.get_name (| globals, "U256" |); Constant.None_ ] |)
)).

Definition K : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
    make_list [
      Constant.str "K"
    ],
    make_dict []
  |)
)).

Definition V : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
    make_list [
      Constant.str "V";
      M.get_subscript (| M.get_name (| globals, "Optional" |), M.get_name (| globals, "Account" |) |);
      M.get_subscript (| M.get_name (| globals, "Optional" |), M.get_name (| globals, "Bytes" |) |);
      M.get_name (| globals, "Bytes" |);
      M.get_subscript (| M.get_name (| globals, "Optional" |), M.get_subscript (| M.get_name (| globals, "Union" |), make_tuple [ M.get_name (| globals, "LegacyTransaction" |); M.get_name (| globals, "Bytes" |) ] |) |);
      M.get_subscript (| M.get_name (| globals, "Optional" |), M.get_subscript (| M.get_name (| globals, "Union" |), make_tuple [ M.get_name (| globals, "Receipt" |); M.get_name (| globals, "Bytes" |) ] |) |);
      M.get_name (| globals, "Uint" |);
      M.get_name (| globals, "U256" |)
    ],
    make_dict []
  |)
)).

Definition LeafNode : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition ExtensionNode : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition BranchNode : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [

    ].

Definition InternalNode : Value.t := M.run ltac:(M.monadic (
  M.get_subscript (| M.get_name (| globals, "Union" |), make_tuple [ M.get_name (| globals, "LeafNode" |); M.get_name (| globals, "ExtensionNode" |); M.get_name (| globals, "BranchNode" |) ] |)
)).

Definition encode_internal_node : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "node" ] |) in
    let _ := Constant.str "
    Encodes a Merkle Trie node into its RLP form. The RLP will then be
    serialized into a `Bytes` and hashed unless it is less that 32 bytes
    when serialized.

    This function also accepts `None`, representing the absence of a node,
    which is encoded to `b""""""`.

    Parameters
    ----------
    node : Optional[InternalNode]
        The node to encode.

    Returns
    -------
    encoded : `rlp.RLP`
        The node encoded as RLP.
    " in
(* At stmt: unsupported node type: AnnAssign *)
    let _ :=
        let _ :=
            let _ :=
                let _ :=
                    let _ := M.raise (| Some(M.call (|
                      M.get_name (| globals, "AssertionError" |),
                      make_list [
                        (* At expr: unsupported node type: JoinedStr *)
                      ],
                      make_dict []
                    |))
                    M.pure Constant.None_
                  )) |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    let encoded :=
      M.call (|
        M.get_field (| M.get_name (| globals, "rlp" |), "encode" |),
        make_list [
          M.get_name (| globals, "unencoded" |)
        ],
        make_dict []
      |) in
    let _ :=
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "keccak256" |),
            make_list [
              M.get_name (| globals, "encoded" |)
            ],
            make_dict []
          |)
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition encode_node : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "node"; "storage_root" ] |) in
    let _ := Constant.str "
    Encode a Node for storage in the Merkle Trie.

    Currently mostly an unimplemented stub.
    " in
    let _ :=
        let _ :=
            let _ :=
                let _ := M.return_ (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "previous_trie" |), "encode_node" |),
                    make_list [
                      M.get_name (| globals, "node" |);
                      M.get_name (| globals, "storage_root" |)
                    ],
                    make_dict []
                  |)
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition Trie : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Subscript *)]
    [

    ]
    [

    ].

Definition copy_trie : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "trie" ] |) in
    let _ := Constant.str "
    Create a copy of `trie`. Since only frozen objects may be stored in tries,
    the contents are reused.

    Parameters
    ----------
    trie: `Trie`
        Trie to copy.

    Returns
    -------
    new_trie : `Trie[K, V]`
        A copy of the trie.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Trie" |),
        make_list [
          M.get_field (| M.get_name (| globals, "trie" |), "secured" |);
          M.get_field (| M.get_name (| globals, "trie" |), "default" |);
          M.call (|
            M.get_field (| M.get_name (| globals, "copy" |), "copy" |),
            make_list [
              M.get_field (| M.get_name (| globals, "trie" |), "_data" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition trie_set : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "trie"; "key"; "value" ] |) in
    let _ := Constant.str "
    Stores an item in a Merkle Trie.

    This method deletes the key if `value == trie.default`, because the Merkle
    Trie represents the default value by omitting it from the trie.

    Parameters
    ----------
    trie: `Trie`
        Trie to store in.
    key : `Bytes`
        Key to lookup.
    value : `V`
        Node to insert at `key`.
    " in
    let _ :=
        let _ := M.assign (|
          M.get_subscript (| M.get_field (| M.get_name (| globals, "trie" |), "_data" |), M.get_name (| globals, "key" |) |),
          M.get_name (| globals, "value" |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition trie_get : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "trie"; "key" ] |) in
    let _ := Constant.str "
    Gets an item from the Merkle Trie.

    This method returns `trie.default` if the key is missing.

    Parameters
    ----------
    trie:
        Trie to lookup in.
    key :
        Key to lookup.

    Returns
    -------
    node : `V`
        Node at `key` in the trie.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "trie" |), "_data" |), "get" |),
        make_list [
          M.get_name (| globals, "key" |);
          M.get_field (| M.get_name (| globals, "trie" |), "default" |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition common_prefix_length : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "a"; "b" ] |) in
    let _ := Constant.str "
    Find the longest common prefix of two sequences.
    " in
    For M.get_name (| globals, "i" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      M.call (|
        M.get_name (| globals, "len" |),
        make_list [
          M.get_name (| globals, "a" |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) do
      let _ :=
          M.pure Constant.None_
        )) |) in
    EndFor.
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "len" |),
        make_list [
          M.get_name (| globals, "a" |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition nibble_list_to_compact : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "x"; "is_leaf" ] |) in
    let _ := Constant.str "
    Compresses nibble-list into a standard byte array with a flag.

    A nibble-list is a list of byte values no greater than `15`. The flag is
    encoded in high nibble of the highest byte. The flag nibble can be broken
    down into two two-bit flags.

    Highest nibble::

        +---+---+----------+--------+
        | _ | _ | is_leaf | parity |
        +---+---+----------+--------+
          3   2      1         0


    The lowest bit of the nibble encodes the parity of the length of the
    remaining nibbles -- `0` when even and `1` when odd. The second lowest bit
    is used to distinguish leaf and extension nodes. The other two bits are not
    used.

    Parameters
    ----------
    x :
        Array of nibbles.
    is_leaf :
        True if this is part of a leaf node, or false if it is an extension
        node.

    Returns
    -------
    compressed : `bytearray`
        Compact byte array.
    " in
    let compact :=
      M.call (|
        M.get_name (| globals, "bytearray" |),
        make_list [],
        make_dict []
      |) in
    let _ :=
        let _ := M.call (|
    M.get_field (| M.get_name (| globals, "compact" |), "append" |),
    make_list [
      BinOp.add (|
        BinOp.mult (|
          Constant.int 16,
          BinOp.add (|
            BinOp.mult (|
              Constant.int 2,
              M.get_name (| globals, "is_leaf" |)
            |),
            Constant.int 1
          |)
        |),
        M.get_subscript (| M.get_name (| globals, "x" |), Constant.int 0 |)
      |)
    ],
    make_dict []
  |) in
        For M.get_name (| globals, "i" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      Constant.int 1;
      M.call (|
        M.get_name (| globals, "len" |),
        make_list [
          M.get_name (| globals, "x" |)
        ],
        make_dict []
      |);
      Constant.int 2
    ],
    make_dict []
  |) do
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, "compact" |), "append" |),
    make_list [
      BinOp.add (|
        BinOp.mult (|
          Constant.int 16,
          M.get_subscript (| M.get_name (| globals, "x" |), M.get_name (| globals, "i" |) |)
        |),
        M.get_subscript (| M.get_name (| globals, "x" |), BinOp.add (|
          M.get_name (| globals, "i" |),
          Constant.int 1
        |) |)
      |)
    ],
    make_dict []
  |) in
        EndFor.
        M.pure Constant.None_
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Bytes" |),
        make_list [
          M.get_name (| globals, "compact" |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition bytes_to_nibble_list : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "bytes_" ] |) in
    let _ := Constant.str "
    Converts a `Bytes` into to a sequence of nibbles (bytes with value < 16).

    Parameters
    ----------
    bytes_:
        The `Bytes` to convert.

    Returns
    -------
    nibble_list : `Bytes`
        The `Bytes` in nibble-list format.
    " in
    let nibble_list :=
      M.call (|
        M.get_name (| globals, "bytearray" |),
        make_list [
          BinOp.mult (|
            Constant.int 2,
            M.call (|
              M.get_name (| globals, "len" |),
              make_list [
                M.get_name (| globals, "bytes_" |)
              ],
              make_dict []
            |)
          |)
        ],
        make_dict []
      |) in
    For make_tuple [ M.get_name (| globals, "byte_index" |); M.get_name (| globals, "byte" |) ] in M.call (|
    M.get_name (| globals, "enumerate" |),
    make_list [
      M.get_name (| globals, "bytes_" |)
    ],
    make_dict []
  |) do
      let _ := M.assign (|
        M.get_subscript (| M.get_name (| globals, "nibble_list" |), BinOp.mult (|
          M.get_name (| globals, "byte_index" |),
          Constant.int 2
        |) |),
        BinOp.r_shift (|
          BinOp.bit_and (|
            M.get_name (| globals, "byte" |),
            Constant.int 240
          |),
          Constant.int 4
        |)
      |) in
      let _ := M.assign (|
        M.get_subscript (| M.get_name (| globals, "nibble_list" |), BinOp.add (|
          BinOp.mult (|
            M.get_name (| globals, "byte_index" |),
            Constant.int 2
          |),
          Constant.int 1
        |) |),
        BinOp.bit_and (|
          M.get_name (| globals, "byte" |),
          Constant.int 15
        |)
      |) in
    EndFor.
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "Bytes" |),
        make_list [
          M.get_name (| globals, "nibble_list" |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition _prepare_trie : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "trie"; "get_storage_root" ] |) in
    let _ := Constant.str "
    Prepares the trie for root calculation. Removes values that are empty,
    hashes the keys (if `secured == True`) and encodes all the nodes.

    Parameters
    ----------
    trie :
        The `Trie` to prepare.
    get_storage_root :
        Function to get the storage root of an account. Needed to encode
        `Account` objects.

    Returns
    -------
    out : `Mapping[ethereum.base_types.Bytes, Node]`
        Object with keys mapped to nibble-byte form.
    " in
(* At stmt: unsupported node type: AnnAssign *)
    For make_tuple [ M.get_name (| globals, "preimage" |); M.get_name (| globals, "value" |) ] in M.call (|
    M.get_field (| M.get_field (| M.get_name (| globals, "trie" |), "_data" |), "items" |),
    make_list [],
    make_dict []
  |) do
      let _ :=
          let encoded_value :=
            M.call (|
              M.get_name (| globals, "encode_node" |),
              make_list [
                M.get_name (| globals, "value" |)
              ],
              make_dict []
            |) in
          M.pure Constant.None_
        )) |) in
      let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.not_eq (|
        M.get_name (| globals, "encoded_value" |),
        Constant.bytes ""
      |);
      M.get_name (| globals, "AssertionError" |)
    ],
    make_dict []
  |) in
(* At stmt: unsupported node type: AnnAssign *)
      let _ :=
          let key :=
            M.get_name (| globals, "preimage" |) in
          M.pure Constant.None_
        )) |) in
      let _ := M.assign (|
        M.get_subscript (| M.get_name (| globals, "mapped" |), M.call (|
          M.get_name (| globals, "bytes_to_nibble_list" |),
          make_list [
            M.get_name (| globals, "key" |)
          ],
          make_dict []
        |) |),
        M.get_name (| globals, "encoded_value" |)
      |) in
    EndFor.
    let _ := M.return_ (|
      M.get_name (| globals, "mapped" |)
    M.pure Constant.None_)).

Definition root : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "trie"; "get_storage_root" ] |) in
    let _ := Constant.str "
    Computes the root of a modified merkle patricia trie (MPT).

    Parameters
    ----------
    trie :
        `Trie` to get the root of.
    get_storage_root :
        Function to get the storage root of an account. Needed to encode
        `Account` objects.


    Returns
    -------
    root : `.fork_types.Root`
        MPT root of the underlying key-value pairs.
    " in
    let obj :=
      M.call (|
        M.get_name (| globals, "_prepare_trie" |),
        make_list [
          M.get_name (| globals, "trie" |);
          M.get_name (| globals, "get_storage_root" |)
        ],
        make_dict []
      |) in
    let root_node :=
      M.call (|
        M.get_name (| globals, "encode_internal_node" |),
        make_list [
          M.call (|
            M.get_name (| globals, "patricialize" |),
            make_list [
              M.get_name (| globals, "obj" |);
              M.call (|
                M.get_name (| globals, "Uint" |),
                make_list [
                  Constant.int 0
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
        let _ := M.assert (| M.call (|
    M.get_name (| globals, "isinstance" |),
    make_list [
      M.get_name (| globals, "root_node" |);
      M.get_name (| globals, "Bytes" |)
    ],
    make_dict []
  |) |) in
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, "Root" |),
            make_list [
              M.get_name (| globals, "root_node" |)
            ],
            make_dict []
          |)
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition patricialize : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "obj"; "level" ] |) in
    let _ := Constant.str "
    Structural composition function.

    Used to recursively patricialize and merkleize a dictionary. Includes
    memoization of the tree structure and hashes.

    Parameters
    ----------
    obj :
        Underlying trie key-value pairs, with keys in nibble-list format.
    level :
        Current trie level.

    Returns
    -------
    node : `ethereum.base_types.Bytes`
        Root node of `obj`.
    " in
    let _ :=
        M.pure Constant.None_
      )) |) in
    let arbitrary_key :=
      M.call (|
        M.get_name (| globals, "next" |),
        make_list [
          M.call (|
            M.get_name (| globals, "iter" |),
            make_list [
              M.get_name (| globals, "obj" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |) in
    let _ :=
        M.pure Constant.None_
      )) |) in
    let substring :=
      M.get_subscript (| M.get_name (| globals, "arbitrary_key" |), M.get_name (| globals, "level" |) |) in
    let prefix_length :=
      M.call (|
        M.get_name (| globals, "len" |),
        make_list [
          M.get_name (| globals, "substring" |)
        ],
        make_dict []
      |) in
    For M.get_name (| globals, "key" |) in M.get_name (| globals, "obj" |) do
      let prefix_length :=
        M.call (|
          M.get_name (| globals, "min" |),
          make_list [
            M.get_name (| globals, "prefix_length" |);
            M.call (|
              M.get_name (| globals, "common_prefix_length" |),
              make_list [
                M.get_name (| globals, "substring" |);
                M.get_subscript (| M.get_name (| globals, "key" |), M.get_name (| globals, "level" |) |)
              ],
              make_dict []
            |)
          ],
          make_dict []
        |) in
      let _ :=
          M.pure Constant.None_
        )) |) in
    EndFor.
    let _ :=
        M.pure Constant.None_
      )) |) in
(* At stmt: unsupported node type: AnnAssign *)
    For M.get_name (| globals, "_" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      Constant.int 16
    ],
    make_dict []
  |) do
      let _ := M.call (|
    M.get_field (| M.get_name (| globals, "branches" |), "append" |),
    make_list [
      {}
    ],
    make_dict []
  |) in
    EndFor.
    let value :=
      Constant.bytes "" in
    For M.get_name (| globals, "key" |) in M.get_name (| globals, "obj" |) do
      let _ :=
          let _ := M.assign (|
            M.get_subscript (| M.get_subscript (| M.get_name (| globals, "branches" |), M.get_subscript (| M.get_name (| globals, "key" |), M.get_name (| globals, "level" |) |) |), M.get_name (| globals, "key" |) |),
            M.get_subscript (| M.get_name (| globals, "obj" |), M.get_name (| globals, "key" |) |)
          |) in
          M.pure Constant.None_
        )) |) in
    EndFor.
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, "BranchNode" |),
        make_list [
          (* At expr: unsupported node type: ListComp *);
          M.get_name (| globals, "value" |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).
