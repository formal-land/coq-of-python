Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.arrow_glacier.trie".

Definition locals_stack : list Locals.t := [].

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

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".
Axiom dataclasses_imports_field :
  IsImported globals "dataclasses" "field".

Axiom typing_imports_Callable :
  IsImported globals "typing" "Callable".
Axiom typing_imports_Dict :
  IsImported globals "typing" "Dict".
Axiom typing_imports_Generic :
  IsImported globals "typing" "Generic".
Axiom typing_imports_List :
  IsImported globals "typing" "List".
Axiom typing_imports_Mapping :
  IsImported globals "typing" "Mapping".
Axiom typing_imports_MutableMapping :
  IsImported globals "typing" "MutableMapping".
Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Sequence :
  IsImported globals "typing" "Sequence".
Axiom typing_imports_TypeVar :
  IsImported globals "typing" "TypeVar".
Axiom typing_imports_Union :
  IsImported globals "typing" "Union".
Axiom typing_imports_cast :
  IsImported globals "typing" "cast".

Axiom ethereum_crypto_hash_imports_keccak256 :
  IsImported globals "ethereum.crypto.hash" "keccak256".

Axiom ethereum_london_imports_trie :
  IsImported globals "ethereum.london" "trie".

Axiom ethereum_utils_ensure_imports_ensure :
  IsImported globals "ethereum.utils.ensure" "ensure".

Axiom ethereum_utils_hexadecimal_imports_hex_to_bytes :
  IsImported globals "ethereum.utils.hexadecimal" "hex_to_bytes".

Axiom ethereum_imports_rlp :
  IsImported globals "ethereum" "rlp".

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".
Axiom ethereum_base_types_imports_slotted_freezable :
  IsImported globals "ethereum.base_types" "slotted_freezable".

Axiom ethereum_arrow_glacier_blocks_imports_Receipt :
  IsImported globals "ethereum.arrow_glacier.blocks" "Receipt".

Axiom ethereum_arrow_glacier_fork_types_imports_Account :
  IsImported globals "ethereum.arrow_glacier.fork_types" "Account".
Axiom ethereum_arrow_glacier_fork_types_imports_Address :
  IsImported globals "ethereum.arrow_glacier.fork_types" "Address".
Axiom ethereum_arrow_glacier_fork_types_imports_Root :
  IsImported globals "ethereum.arrow_glacier.fork_types" "Root".
Axiom ethereum_arrow_glacier_fork_types_imports_encode_account :
  IsImported globals "ethereum.arrow_glacier.fork_types" "encode_account".

Axiom ethereum_arrow_glacier_transactions_imports_LegacyTransaction :
  IsImported globals "ethereum.arrow_glacier.transactions" "LegacyTransaction".

Definition EMPTY_TRIE_ROOT : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "Root" |),
    make_list [
      M.call (|
        M.get_name (| globals, locals_stack, "hex_to_bytes" |),
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
  M.get_subscript (|
    M.get_name (| globals, locals_stack, "Union" |),
    make_tuple [ M.get_name (| globals, locals_stack, "Account" |); M.get_name (| globals, locals_stack, "Bytes" |); M.get_name (| globals, locals_stack, "LegacyTransaction" |); M.get_name (| globals, locals_stack, "Receipt" |); M.get_name (| globals, locals_stack, "Uint" |); M.get_name (| globals, locals_stack, "U256" |); Constant.None_ ]
  |)
)).

Definition K : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "K"
    ],
    make_dict []
  |)
)).

Definition V : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "V";
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "Optional" |),
        M.get_name (| globals, locals_stack, "Account" |)
      |);
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "Optional" |),
        M.get_name (| globals, locals_stack, "Bytes" |)
      |);
      M.get_name (| globals, locals_stack, "Bytes" |);
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "Optional" |),
        M.get_subscript (|
          M.get_name (| globals, locals_stack, "Union" |),
          make_tuple [ M.get_name (| globals, locals_stack, "LegacyTransaction" |); M.get_name (| globals, locals_stack, "Bytes" |) ]
        |)
      |);
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "Optional" |),
        M.get_subscript (|
          M.get_name (| globals, locals_stack, "Union" |),
          make_tuple [ M.get_name (| globals, locals_stack, "Receipt" |); M.get_name (| globals, locals_stack, "Bytes" |) ]
        |)
      |);
      M.get_name (| globals, locals_stack, "Uint" |);
      M.get_name (| globals, locals_stack, "U256" |)
    ],
    make_dict []
  |)
)).

Definition LeafNode : Value.t := make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition ExtensionNode : Value.t := make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition BranchNode : Value.t := make_klass {|
  Klass.bases := [
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition InternalNode : Value.t := M.run ltac:(M.monadic (
  M.get_subscript (|
    M.get_name (| globals, locals_stack, "Union" |),
    make_tuple [ M.get_name (| globals, locals_stack, "LeafNode" |); M.get_name (| globals, locals_stack, "ExtensionNode" |); M.get_name (| globals, locals_stack, "BranchNode" |) ]
  |)
)).

Definition encode_internal_node : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "node" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Encodes a Merkle Trie node into its RLP form. The RLP will then be
    serialized into a `Bytes` and hashed unless it is less that 32 bytes
    when serialized.

    This function also accepts `None`, representing the absence of a node,
    which is encoded to `b""""`.

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
      (* if *)
      M.if_then_else (|
        Compare.is (|
          M.get_name (| globals, locals_stack, "node" |),
          Constant.None_
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "unencoded" ,
          Constant.bytes ""
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
                M.get_name (| globals, locals_stack, "node" |);
                M.get_name (| globals, locals_stack, "LeafNode" |)
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "unencoded" ,
              make_tuple [ M.call (|
                M.get_name (| globals, locals_stack, "nibble_list_to_compact" |),
                make_list [
                  M.get_field (| M.get_name (| globals, locals_stack, "node" |), "rest_of_key" |);
                  Constant.bool true
                ],
                make_dict []
              |); M.get_field (| M.get_name (| globals, locals_stack, "node" |), "value" |) ]
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
                    M.get_name (| globals, locals_stack, "node" |);
                    M.get_name (| globals, locals_stack, "ExtensionNode" |)
                  ],
                  make_dict []
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.assign_local (|
                  "unencoded" ,
                  make_tuple [ M.call (|
                    M.get_name (| globals, locals_stack, "nibble_list_to_compact" |),
                    make_list [
                      M.get_field (| M.get_name (| globals, locals_stack, "node" |), "key_segment" |);
                      Constant.bool false
                    ],
                    make_dict []
                  |); M.get_field (| M.get_name (| globals, locals_stack, "node" |), "subnode" |) ]
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
                        M.get_name (| globals, locals_stack, "node" |);
                        M.get_name (| globals, locals_stack, "BranchNode" |)
                      ],
                      make_dict []
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.assign_local (|
                      "unencoded" ,
                      BinOp.add (|
                        M.get_field (| M.get_name (| globals, locals_stack, "node" |), "subnodes" |),
                        make_list [
                          M.get_field (| M.get_name (| globals, locals_stack, "node" |), "value" |)
                        ]
                      |)
                    |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    let _ := M.raise (| Some (M.call (|
                      M.get_name (| globals, locals_stack, "AssertionError" |),
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
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "encoded" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
        make_list [
          M.get_name (| globals, locals_stack, "unencoded" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "encoded" |)
            ],
            make_dict []
          |),
          Constant.int 32
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "unencoded" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "keccak256" |),
            make_list [
              M.get_name (| globals, locals_stack, "encoded" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom encode_internal_node_in_globals :
  IsInGlobals globals "encode_internal_node" (make_function encode_internal_node).

Definition encode_node : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "node"; "storage_root" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Encode a Node for storage in the Merkle Trie.

    Currently mostly an unimplemented stub.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "isinstance" |),
          make_list [
            M.get_name (| globals, locals_stack, "node" |);
            M.get_name (| globals, locals_stack, "Account" |)
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assert (| Compare.is_not (|
    M.get_name (| globals, locals_stack, "storage_root" |),
    Constant.None_
  |) |) in
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "encode_account" |),
            make_list [
              M.get_name (| globals, locals_stack, "node" |);
              M.get_name (| globals, locals_stack, "storage_root" |)
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
                M.get_name (| globals, locals_stack, "node" |);
                make_tuple [ M.get_name (| globals, locals_stack, "LegacyTransaction" |); M.get_name (| globals, locals_stack, "Receipt" |); M.get_name (| globals, locals_stack, "U256" |) ]
              ],
              make_dict []
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
                make_list [
                  M.call (|
                    M.get_name (| globals, locals_stack, "cast" |),
                    make_list [
                      M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "RLP" |);
                      M.get_name (| globals, locals_stack, "node" |)
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
                    M.get_name (| globals, locals_stack, "node" |);
                    M.get_name (| globals, locals_stack, "Bytes" |)
                  ],
                  make_dict []
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (|
                  M.get_name (| globals, locals_stack, "node" |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ := M.return_ (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "previous_trie" |), "encode_node" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "node" |);
                      M.get_name (| globals, locals_stack, "storage_root" |)
                    ],
                    make_dict []
                  |)
                |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom encode_node_in_globals :
  IsInGlobals globals "encode_node" (make_function encode_node).

Definition Trie : Value.t := make_klass {|
  Klass.bases := [
    (globals, "(* At base: unsupported node type: Subscript *)")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition copy_trie : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "trie" ] in
    ltac:(M.monadic (
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
        M.get_name (| globals, locals_stack, "Trie" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "secured" |);
          M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "default" |);
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "copy" |), "copy" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "_data" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom copy_trie_in_globals :
  IsInGlobals globals "copy_trie" (make_function copy_trie).

Definition trie_set : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "trie"; "key"; "value" ] in
    ltac:(M.monadic (
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
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.get_name (| globals, locals_stack, "value" |),
          M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "default" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.in_ (|
              M.get_name (| globals, locals_stack, "key" |),
              M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "_data" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.delete (| M.get_subscript (|
    M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "_data" |),
    M.get_name (| globals, locals_stack, "key" |)
  |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.assign (|
          M.get_subscript (|
            M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "_data" |),
            M.get_name (| globals, locals_stack, "key" |)
          |),
          M.get_name (| globals, locals_stack, "value" |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom trie_set_in_globals :
  IsInGlobals globals "trie_set" (make_function trie_set).

Definition trie_get : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "trie"; "key" ] in
    ltac:(M.monadic (
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
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "_data" |), "get" |),
        make_list [
          M.get_name (| globals, locals_stack, "key" |);
          M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "default" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom trie_get_in_globals :
  IsInGlobals globals "trie_get" (make_function trie_get).

Definition common_prefix_length : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "a"; "b" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Find the longest common prefix of two sequences.
    " in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "i" |),
        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_name (| globals, locals_stack, "a" |)
          ],
          make_dict []
        |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.gt_e (|
                  M.get_name (| globals, locals_stack, "i" |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "b" |)
                    ],
                    make_dict []
                  |)
                |),
                ltac:(M.monadic (
                  Compare.not_eq (|
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "a" |),
                      M.get_name (| globals, locals_stack, "i" |)
                    |),
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "b" |),
                      M.get_name (| globals, locals_stack, "i" |)
                    |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, locals_stack, "i" |)
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
      M.call (|
        M.get_name (| globals, locals_stack, "len" |),
        make_list [
          M.get_name (| globals, locals_stack, "a" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom common_prefix_length_in_globals :
  IsInGlobals globals "common_prefix_length" (make_function common_prefix_length).

Definition nibble_list_to_compact : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "x"; "is_leaf" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "compact" ,
      M.call (|
        M.get_name (| globals, locals_stack, "bytearray" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          BinOp.mod_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                M.get_name (| globals, locals_stack, "x" |)
              ],
              make_dict []
            |),
            Constant.int 2
          |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "compact" |), "append" |),
    make_list [
      BinOp.mult (|
        Constant.int 16,
        BinOp.mult (|
          Constant.int 2,
          M.get_name (| globals, locals_stack, "is_leaf" |)
        |)
      |)
    ],
    make_dict []
  |) in
        let _ :=
          M.for_ (|
            M.get_name (| globals, locals_stack, "i" |),
            M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        Constant.int 0;
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_name (| globals, locals_stack, "x" |)
          ],
          make_dict []
        |);
        Constant.int 2
      ],
      make_dict []
    |),
            ltac:(M.monadic (
              let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "compact" |), "append" |),
    make_list [
      BinOp.add (|
        BinOp.mult (|
          Constant.int 16,
          M.get_subscript (|
            M.get_name (| globals, locals_stack, "x" |),
            M.get_name (| globals, locals_stack, "i" |)
          |)
        |),
        M.get_subscript (|
          M.get_name (| globals, locals_stack, "x" |),
          BinOp.add (|
            M.get_name (| globals, locals_stack, "i" |),
            Constant.int 1
          |)
        |)
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
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "compact" |), "append" |),
    make_list [
      BinOp.add (|
        BinOp.mult (|
          Constant.int 16,
          BinOp.add (|
            BinOp.mult (|
              Constant.int 2,
              M.get_name (| globals, locals_stack, "is_leaf" |)
            |),
            Constant.int 1
          |)
        |),
        M.get_subscript (|
          M.get_name (| globals, locals_stack, "x" |),
          Constant.int 0
        |)
      |)
    ],
    make_dict []
  |) in
        let _ :=
          M.for_ (|
            M.get_name (| globals, locals_stack, "i" |),
            M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        Constant.int 1;
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_name (| globals, locals_stack, "x" |)
          ],
          make_dict []
        |);
        Constant.int 2
      ],
      make_dict []
    |),
            ltac:(M.monadic (
              let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "compact" |), "append" |),
    make_list [
      BinOp.add (|
        BinOp.mult (|
          Constant.int 16,
          M.get_subscript (|
            M.get_name (| globals, locals_stack, "x" |),
            M.get_name (| globals, locals_stack, "i" |)
          |)
        |),
        M.get_subscript (|
          M.get_name (| globals, locals_stack, "x" |),
          BinOp.add (|
            M.get_name (| globals, locals_stack, "i" |),
            Constant.int 1
          |)
        |)
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
      )) |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "compact" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom nibble_list_to_compact_in_globals :
  IsInGlobals globals "nibble_list_to_compact" (make_function nibble_list_to_compact).

Definition bytes_to_nibble_list : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "bytes_" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "nibble_list" ,
      M.call (|
        M.get_name (| globals, locals_stack, "bytearray" |),
        make_list [
          BinOp.mult (|
            Constant.int 2,
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                M.get_name (| globals, locals_stack, "bytes_" |)
              ],
              make_dict []
            |)
          |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      M.for_ (|
        make_tuple [ M.get_name (| globals, locals_stack, "byte_index" |); M.get_name (| globals, locals_stack, "byte" |) ],
        M.call (|
      M.get_name (| globals, locals_stack, "enumerate" |),
      make_list [
        M.get_name (| globals, locals_stack, "bytes_" |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "nibble_list" |),
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "byte_index" |),
                Constant.int 2
              |)
            |),
            BinOp.r_shift (|
              BinOp.bit_and (|
                M.get_name (| globals, locals_stack, "byte" |),
                Constant.int 240
              |),
              Constant.int 4
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "nibble_list" |),
              BinOp.add (|
                BinOp.mult (|
                  M.get_name (| globals, locals_stack, "byte_index" |),
                  Constant.int 2
                |),
                Constant.int 1
              |)
            |),
            BinOp.bit_and (|
              M.get_name (| globals, locals_stack, "byte" |),
              Constant.int 15
            |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "Bytes" |),
        make_list [
          M.get_name (| globals, locals_stack, "nibble_list" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom bytes_to_nibble_list_in_globals :
  IsInGlobals globals "bytes_to_nibble_list" (make_function bytes_to_nibble_list).

Definition _prepare_trie : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "trie"; "get_storage_root" ] in
    ltac:(M.monadic (
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
    let _ :=
      M.for_ (|
        make_tuple [ M.get_name (| globals, locals_stack, "preimage" |); M.get_name (| globals, locals_stack, "value" |) ],
        M.call (|
      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "_data" |), "items" |),
      make_list [],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "value" |);
                  M.get_name (| globals, locals_stack, "Account" |)
                ],
                make_dict []
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.assert (| Compare.is_not (|
    M.get_name (| globals, locals_stack, "get_storage_root" |),
    Constant.None_
  |) |) in
              let _ := M.assign_local (|
                "address" ,
                M.call (|
                  M.get_name (| globals, locals_stack, "Address" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "preimage" |)
                  ],
                  make_dict []
                |)
              |) in
              let _ := M.assign_local (|
                "encoded_value" ,
                M.call (|
                  M.get_name (| globals, locals_stack, "encode_node" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "value" |);
                    M.call (|
                      M.get_name (| globals, locals_stack, "get_storage_root" |),
                      make_list [
                        M.get_name (| globals, locals_stack, "address" |)
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
              let _ := M.assign_local (|
                "encoded_value" ,
                M.call (|
                  M.get_name (| globals, locals_stack, "encode_node" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "value" |)
                  ],
                  make_dict []
                |)
              |) in
              M.pure Constant.None_
            )) |) in
          let _ := M.call (|
    M.get_name (| globals, locals_stack, "ensure" |),
    make_list [
      Compare.not_eq (|
        M.get_name (| globals, locals_stack, "encoded_value" |),
        Constant.bytes ""
      |);
      M.get_name (| globals, locals_stack, "AssertionError" |)
    ],
    make_dict []
  |) in
(* At stmt: unsupported node type: AnnAssign *)
          let _ :=
            (* if *)
            M.if_then_else (|
              M.get_field (| M.get_name (| globals, locals_stack, "trie" |), "secured" |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.assign_local (|
                "key" ,
                M.call (|
                  M.get_name (| globals, locals_stack, "keccak256" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "preimage" |)
                  ],
                  make_dict []
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              let _ := M.assign_local (|
                "key" ,
                M.get_name (| globals, locals_stack, "preimage" |)
              |) in
              M.pure Constant.None_
            )) |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "mapped" |),
              M.call (|
                M.get_name (| globals, locals_stack, "bytes_to_nibble_list" |),
                make_list [
                  M.get_name (| globals, locals_stack, "key" |)
                ],
                make_dict []
              |)
            |),
            M.get_name (| globals, locals_stack, "encoded_value" |)
          |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "mapped" |)
    |) in
    M.pure Constant.None_)).

Axiom _prepare_trie_in_globals :
  IsInGlobals globals "_prepare_trie" (make_function _prepare_trie).

Definition root : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "trie"; "get_storage_root" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "obj" ,
      M.call (|
        M.get_name (| globals, locals_stack, "_prepare_trie" |),
        make_list [
          M.get_name (| globals, locals_stack, "trie" |);
          M.get_name (| globals, locals_stack, "get_storage_root" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "root_node" ,
      M.call (|
        M.get_name (| globals, locals_stack, "encode_internal_node" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "patricialize" |),
            make_list [
              M.get_name (| globals, locals_stack, "obj" |);
              M.call (|
                M.get_name (| globals, locals_stack, "Uint" |),
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
      |)
    |) in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.lt (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
                make_list [
                  M.get_name (| globals, locals_stack, "root_node" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |),
          Constant.int 32
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "keccak256" |),
            make_list [
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "rlp" |), "encode" |),
                make_list [
                  M.get_name (| globals, locals_stack, "root_node" |)
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
        let _ := M.assert (| M.call (|
    M.get_name (| globals, locals_stack, "isinstance" |),
    make_list [
      M.get_name (| globals, locals_stack, "root_node" |);
      M.get_name (| globals, locals_stack, "Bytes" |)
    ],
    make_dict []
  |) |) in
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "Root" |),
            make_list [
              M.get_name (| globals, locals_stack, "root_node" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom root_in_globals :
  IsInGlobals globals "root" (make_function root).

Definition patricialize : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "obj"; "level" ] in
    ltac:(M.monadic (
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
      (* if *)
      M.if_then_else (|
        Compare.eq (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "obj" |)
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
    let _ := M.assign_local (|
      "arbitrary_key" ,
      M.call (|
        M.get_name (| globals, locals_stack, "next" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "iter" |),
            make_list [
              M.get_name (| globals, locals_stack, "obj" |)
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
        Compare.eq (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "obj" |)
            ],
            make_dict []
          |),
          Constant.int 1
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "leaf" ,
          M.call (|
            M.get_name (| globals, locals_stack, "LeafNode" |),
            make_list [
              M.slice (|
                M.get_name (| globals, locals_stack, "arbitrary_key" |),
                M.get_name (| globals, locals_stack, "level" |),
                Constant.None_,
                Constant.None_
              |);
              M.get_subscript (|
                M.get_name (| globals, locals_stack, "obj" |),
                M.get_name (| globals, locals_stack, "arbitrary_key" |)
              |)
            ],
            make_dict []
          |)
        |) in
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "leaf" |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "substring" ,
      M.slice (|
        M.get_name (| globals, locals_stack, "arbitrary_key" |),
        M.get_name (| globals, locals_stack, "level" |),
        Constant.None_,
        Constant.None_
      |)
    |) in
    let _ := M.assign_local (|
      "prefix_length" ,
      M.call (|
        M.get_name (| globals, locals_stack, "len" |),
        make_list [
          M.get_name (| globals, locals_stack, "substring" |)
        ],
        make_dict []
      |)
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "key" |),
        M.get_name (| globals, locals_stack, "obj" |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "prefix_length" ,
            M.call (|
              M.get_name (| globals, locals_stack, "min" |),
              make_list [
                M.get_name (| globals, locals_stack, "prefix_length" |);
                M.call (|
                  M.get_name (| globals, locals_stack, "common_prefix_length" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "substring" |);
                    M.slice (|
                      M.get_name (| globals, locals_stack, "key" |),
                      M.get_name (| globals, locals_stack, "level" |),
                      Constant.None_,
                      Constant.None_
                    |)
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
              Compare.eq (|
                M.get_name (| globals, locals_stack, "prefix_length" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.break (| |) in
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
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.gt (|
          M.get_name (| globals, locals_stack, "prefix_length" |),
          Constant.int 0
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "prefix" ,
          M.slice (|
            M.get_name (| globals, locals_stack, "arbitrary_key" |),
            M.get_name (| globals, locals_stack, "level" |),
            BinOp.add (|
              M.get_name (| globals, locals_stack, "level" |),
              M.get_name (| globals, locals_stack, "prefix_length" |)
            |),
            Constant.None_
          |)
        |) in
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "ExtensionNode" |),
            make_list [
              M.get_name (| globals, locals_stack, "prefix" |);
              M.call (|
                M.get_name (| globals, locals_stack, "encode_internal_node" |),
                make_list [
                  M.call (|
                    M.get_name (| globals, locals_stack, "patricialize" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "obj" |);
                      BinOp.add (|
                        M.get_name (| globals, locals_stack, "level" |),
                        M.get_name (| globals, locals_stack, "prefix_length" |)
                      |)
                    ],
                    make_dict []
                  |)
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
(* At stmt: unsupported node type: AnnAssign *)
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "_" |),
        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        Constant.int 16
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "branches" |), "append" |),
    make_list [
      Constant.str "(* At expr: unsupported node type: Dict *)"
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
      "value" ,
      Constant.bytes ""
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "key" |),
        M.get_name (| globals, locals_stack, "obj" |),
        ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.eq (|
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "key" |)
                  ],
                  make_dict []
                |),
                M.get_name (| globals, locals_stack, "level" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ :=
                (* if *)
                M.if_then_else (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "isinstance" |),
                    make_list [
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "obj" |),
                        M.get_name (| globals, locals_stack, "key" |)
                      |);
                      make_tuple [ M.get_name (| globals, locals_stack, "Account" |); M.get_name (| globals, locals_stack, "Receipt" |); M.get_name (| globals, locals_stack, "Uint" |) ]
                    ],
                    make_dict []
                  |),
                (* then *)
                ltac:(M.monadic (
                  let _ := M.raise (| Some (M.get_name (| globals, locals_stack, "AssertionError" |)) |) in
                  M.pure Constant.None_
                (* else *)
                )), ltac:(M.monadic (
                  M.pure Constant.None_
                )) |) in
              let _ := M.assign_local (|
                "value" ,
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "obj" |),
                  M.get_name (| globals, locals_stack, "key" |)
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              let _ := M.assign (|
                M.get_subscript (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "branches" |),
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "key" |),
                      M.get_name (| globals, locals_stack, "level" |)
                    |)
                  |),
                  M.get_name (| globals, locals_stack, "key" |)
                |),
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "obj" |),
                  M.get_name (| globals, locals_stack, "key" |)
                |)
              |) in
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "BranchNode" |),
        make_list [
          Constant.str "(* At expr: unsupported node type: ListComp *)";
          M.get_name (| globals, locals_stack, "value" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom patricialize_in_globals :
  IsInGlobals globals "patricialize" (make_function patricialize).
