Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
The Blake2 Implementation
^^^^^^^^^^^^^^^^^^^^^^^^^^
".

(* At top_level_stmt: unsupported node type: Import *)

Require dataclasses.
Axiom dataclasses_dataclass :
  IsGlobalAlias globals dataclasses.globals "dataclass".

Require typing.
Axiom typing_List :
  IsGlobalAlias globals typing.globals "List".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".

Require ethereum.base_types.
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Definition spit_le_to_uint : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "data"; "start"; "num_words" ] |) in
    let _ := Constant.str "
    Extracts 8 byte words from a given data.

    Parameters
    ----------
    data :
        The data in bytes from which the words need to be extracted
    start :
        Position to start the extraction
    num_words:
        The number of words to be extracted
    " in
    let words :=
      make_list [] in
    For M.get_name (| globals, "i" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      M.get_name (| globals, "num_words" |)
    ],
    make_dict []
  |) do
      let start_position :=
        BinOp.add (|
          M.get_name (| globals, "start" |),
          BinOp.mult (|
            M.get_name (| globals, "i" |),
            Constant.int 8
          |)
        |) in
      let _ := M.call (|
    M.get_field (| M.get_name (| globals, "words" |), "append" |),
    make_list [
      M.call (|
        M.get_field (| M.get_name (| globals, "Uint" |), "from_le_bytes" |),
        make_list [
          M.get_subscript (| M.get_name (| globals, "data" |), M.get_name (| globals, "start_position" |) |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |) in
    EndFor.
    let _ := M.return_ (|
      M.get_name (| globals, "words" |)
    M.pure Constant.None_)).

Definition Blake2 : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [
      (
        "get_blake2_parameters",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "data" ] |) in
          let _ := Constant.str "
        Extract the parameters required in the Blake2 compression function
        from the provided bytes data.

        Parameters
        ----------
        data :
            The bytes data that has been passed in the message.
        " in
          let rounds :=
            M.call (|
              M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
              make_list [
                M.get_subscript (| M.get_name (| globals, "data" |), Constant.None_:Constant.int 4 |)
              ],
              make_dict []
            |) in
          let h :=
            M.call (|
              M.get_name (| globals, "spit_le_to_uint" |),
              make_list [
                M.get_name (| globals, "data" |);
                Constant.int 4;
                Constant.int 8
              ],
              make_dict []
            |) in
          let m :=
            M.call (|
              M.get_name (| globals, "spit_le_to_uint" |),
              make_list [
                M.get_name (| globals, "data" |);
                Constant.int 68;
                Constant.int 16
              ],
              make_dict []
            |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, "t_0" |); M.get_name (| globals, "t_1" |) ],
            M.call (|
              M.get_name (| globals, "spit_le_to_uint" |),
              make_list [
                M.get_name (| globals, "data" |);
                Constant.int 196;
                Constant.int 2
              ],
              make_dict []
            |)
          |) in
          let f :=
            M.call (|
              M.get_field (| M.get_name (| globals, "Uint" |), "from_be_bytes" |),
              make_list [
                M.get_subscript (| M.get_name (| globals, "data" |), Constant.int 212 |)
              ],
              make_dict []
            |) in
          let _ := M.return_ (|
            make_tuple [ M.get_name (| globals, "rounds" |); M.get_name (| globals, "h" |); M.get_name (| globals, "m" |); M.get_name (| globals, "t_0" |); M.get_name (| globals, "t_1" |); M.get_name (| globals, "f" |) ]
          M.pure Constant.None_))
      );
      (
        "G",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "v"; "a"; "b"; "c"; "d"; "x"; "y" ] |) in
          let _ := Constant.str "
        The mixing function used in Blake2
        https://datatracker.ietf.org/doc/html/rfc7693#section-3.1

        Parameters
        ----------
        v :
            The working vector to be mixed.
        a, b, c, d :
            Indexes within v of the words to be mixed.
        x, y :
            The two input words for the mixing.
        " in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "a" |) |),
            BinOp.mod_ (|
              BinOp.add (|
                BinOp.add (|
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "a" |) |),
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "b" |) |)
                |),
                M.get_name (| globals, "x" |)
              |),
              M.get_field (| M.get_name (| globals, "self" |), "max_word" |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "d" |) |),
            BinOp.bit_xor (|
              BinOp.r_shift (|
                BinOp.bit_xor (|
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "d" |) |),
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "a" |) |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "R1" |)
              |),
              BinOp.mod_ (|
                BinOp.l_shift (|
                  BinOp.bit_xor (|
                    M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "d" |) |),
                    M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "a" |) |)
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "w_R1" |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "max_word" |)
              |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "c" |) |),
            BinOp.mod_ (|
              BinOp.add (|
                M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "c" |) |),
                M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "d" |) |)
              |),
              M.get_field (| M.get_name (| globals, "self" |), "max_word" |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "b" |) |),
            BinOp.bit_xor (|
              BinOp.r_shift (|
                BinOp.bit_xor (|
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "b" |) |),
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "c" |) |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "R2" |)
              |),
              BinOp.mod_ (|
                BinOp.l_shift (|
                  BinOp.bit_xor (|
                    M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "b" |) |),
                    M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "c" |) |)
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "w_R2" |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "max_word" |)
              |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "a" |) |),
            BinOp.mod_ (|
              BinOp.add (|
                BinOp.add (|
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "a" |) |),
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "b" |) |)
                |),
                M.get_name (| globals, "y" |)
              |),
              M.get_field (| M.get_name (| globals, "self" |), "max_word" |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "d" |) |),
            BinOp.bit_xor (|
              BinOp.r_shift (|
                BinOp.bit_xor (|
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "d" |) |),
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "a" |) |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "R3" |)
              |),
              BinOp.mod_ (|
                BinOp.l_shift (|
                  BinOp.bit_xor (|
                    M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "d" |) |),
                    M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "a" |) |)
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "w_R3" |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "max_word" |)
              |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "c" |) |),
            BinOp.mod_ (|
              BinOp.add (|
                M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "c" |) |),
                M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "d" |) |)
              |),
              M.get_field (| M.get_name (| globals, "self" |), "max_word" |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "b" |) |),
            BinOp.bit_xor (|
              BinOp.r_shift (|
                BinOp.bit_xor (|
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "b" |) |),
                  M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "c" |) |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "R4" |)
              |),
              BinOp.mod_ (|
                BinOp.l_shift (|
                  BinOp.bit_xor (|
                    M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "b" |) |),
                    M.get_subscript (| M.get_name (| globals, "v" |), M.get_name (| globals, "c" |) |)
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "w_R4" |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "max_word" |)
              |)
            |)
          |) in
          let _ := M.return_ (|
            M.get_name (| globals, "v" |)
          M.pure Constant.None_))
      );
      (
        "compress",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "num_rounds"; "h"; "m"; "t_0"; "t_1"; "f" ] |) in
          let _ := Constant.str "
        'F Compression' from section 3.2 of RFC 7693:
        https://tools.ietf.org/html/rfc7693#section-3.2

        Parameters
        ----------
        num_rounds :
            The number of rounds. A 32-bit unsigned big-endian word
        h :
            The state vector. 8 unsigned 64-bit little-endian words
        m :
            The message block vector. 16 unsigned 64-bit little-endian words
        t_0, t_1 :
            Offset counters. 2 unsigned 64-bit little-endian words
        f:
            The final block indicator flag. An 8-bit word
        " in
          let v :=
            BinOp.mult (|
              make_list [
                Constant.int 0
              ],
              Constant.int 16
            |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), Constant.int 0 |),
            M.get_name (| globals, "h" |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), Constant.int 8 |),
            M.get_field (| M.get_name (| globals, "self" |), "IV" |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), Constant.int 12 |),
            BinOp.bit_xor (|
              M.get_name (| globals, "t_0" |),
              M.get_subscript (| M.get_field (| M.get_name (| globals, "self" |), "IV" |), Constant.int 4 |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (| M.get_name (| globals, "v" |), Constant.int 13 |),
            BinOp.bit_xor (|
              M.get_name (| globals, "t_1" |),
              M.get_subscript (| M.get_field (| M.get_name (| globals, "self" |), "IV" |), Constant.int 5 |)
            |)
          |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          For M.get_name (| globals, "r" |) in M.call (|
    M.get_name (| globals, "range" |),
    make_list [
      M.get_name (| globals, "num_rounds" |)
    ],
    make_dict []
  |) do
            let s :=
              M.get_subscript (| M.get_field (| M.get_name (| globals, "self" |), "sigma" |), BinOp.mod_ (|
                M.get_name (| globals, "r" |),
                M.get_field (| M.get_name (| globals, "self" |), "sigma_len" |)
              |) |) in
            let v :=
              M.call (|
                M.get_field (| M.get_name (| globals, "self" |), "G" |),
                make_list [
                  M.get_name (| globals, "v" |);
                  Constant.int 0;
                  Constant.int 4;
                  Constant.int 8;
                  Constant.int 12;
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 0 |) |);
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 1 |) |)
                ],
                make_dict []
              |) in
            let v :=
              M.call (|
                M.get_field (| M.get_name (| globals, "self" |), "G" |),
                make_list [
                  M.get_name (| globals, "v" |);
                  Constant.int 1;
                  Constant.int 5;
                  Constant.int 9;
                  Constant.int 13;
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 2 |) |);
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 3 |) |)
                ],
                make_dict []
              |) in
            let v :=
              M.call (|
                M.get_field (| M.get_name (| globals, "self" |), "G" |),
                make_list [
                  M.get_name (| globals, "v" |);
                  Constant.int 2;
                  Constant.int 6;
                  Constant.int 10;
                  Constant.int 14;
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 4 |) |);
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 5 |) |)
                ],
                make_dict []
              |) in
            let v :=
              M.call (|
                M.get_field (| M.get_name (| globals, "self" |), "G" |),
                make_list [
                  M.get_name (| globals, "v" |);
                  Constant.int 3;
                  Constant.int 7;
                  Constant.int 11;
                  Constant.int 15;
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 6 |) |);
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 7 |) |)
                ],
                make_dict []
              |) in
            let v :=
              M.call (|
                M.get_field (| M.get_name (| globals, "self" |), "G" |),
                make_list [
                  M.get_name (| globals, "v" |);
                  Constant.int 0;
                  Constant.int 5;
                  Constant.int 10;
                  Constant.int 15;
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 8 |) |);
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 9 |) |)
                ],
                make_dict []
              |) in
            let v :=
              M.call (|
                M.get_field (| M.get_name (| globals, "self" |), "G" |),
                make_list [
                  M.get_name (| globals, "v" |);
                  Constant.int 1;
                  Constant.int 6;
                  Constant.int 11;
                  Constant.int 12;
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 10 |) |);
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 11 |) |)
                ],
                make_dict []
              |) in
            let v :=
              M.call (|
                M.get_field (| M.get_name (| globals, "self" |), "G" |),
                make_list [
                  M.get_name (| globals, "v" |);
                  Constant.int 2;
                  Constant.int 7;
                  Constant.int 8;
                  Constant.int 13;
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 12 |) |);
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 13 |) |)
                ],
                make_dict []
              |) in
            let v :=
              M.call (|
                M.get_field (| M.get_name (| globals, "self" |), "G" |),
                make_list [
                  M.get_name (| globals, "v" |);
                  Constant.int 3;
                  Constant.int 4;
                  Constant.int 9;
                  Constant.int 14;
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 14 |) |);
                  M.get_subscript (| M.get_name (| globals, "m" |), M.get_subscript (| M.get_name (| globals, "s" |), Constant.int 15 |) |)
                ],
                make_dict []
              |) in
          EndFor.
          let result_message_words :=
            (* At expr: unsupported node type: GeneratorExp *) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "struct" |), "pack" |),
              make_list_concat (| [
                make_list [
                  BinOp.mod_ (|
                    Constant.str "<8%s",
                    M.get_field (| M.get_name (| globals, "self" |), "word_format" |)
                  |)
                ];
                M.get_name (| globals, "result_message_words" |)
              ] |),
              make_dict []
            |)
          M.pure Constant.None_))
      )
    ].

Definition Blake2b : Value.t :=
  builtins.make_klass
    [(globals, "Blake2")]
    [

    ]
    [

    ].
