Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.crypto.blake2".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
The Blake2 Implementation
^^^^^^^^^^^^^^^^^^^^^^^^^^
".

(* At top_level_stmt: unsupported node type: Import *)

Axiom dataclasses_imports_dataclass :
  IsImported globals "dataclasses" "dataclass".

Axiom typing_imports_List :
  IsImported globals "typing" "List".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".

Axiom ethereum_base_types_imports_Uint :
  IsImported globals "ethereum.base_types" "Uint".

Definition spit_le_to_uint : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "data"; "start"; "num_words" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "words" ,
      make_list []
    |) in
    let _ :=
      M.for_ (|
        M.get_name (| globals, locals_stack, "i" |),
        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.get_name (| globals, locals_stack, "num_words" |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "start_position" ,
            BinOp.add (|
              M.get_name (| globals, locals_stack, "start" |),
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "i" |),
                Constant.int 8
              |)
            |)
          |) in
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "words" |), "append" |),
    make_list [
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_le_bytes" |),
        make_list [
          M.slice (|
            M.get_name (| globals, locals_stack, "data" |),
            M.get_name (| globals, locals_stack, "start_position" |),
            BinOp.add (|
              M.get_name (| globals, locals_stack, "start_position" |),
              Constant.int 8
            |),
            Constant.None_
          |)
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
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "words" |)
    |) in
    M.pure Constant.None_)).

Definition Blake2 : Value.t :=
  builtins.make_klass
    []
    [

    ]
    [
      (
        "get_blake2_parameters",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "data" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Extract the parameters required in the Blake2 compression function
        from the provided bytes data.

        Parameters
        ----------
        data :
            The bytes data that has been passed in the message.
        " in
          let _ := M.assign_local (|
            "rounds" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
              make_list [
                M.slice (|
                  M.get_name (| globals, locals_stack, "data" |),
                  Constant.None_,
                  Constant.int 4,
                  Constant.None_
                |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "h" ,
            M.call (|
              M.get_name (| globals, locals_stack, "spit_le_to_uint" |),
              make_list [
                M.get_name (| globals, locals_stack, "data" |);
                Constant.int 4;
                Constant.int 8
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "m" ,
            M.call (|
              M.get_name (| globals, locals_stack, "spit_le_to_uint" |),
              make_list [
                M.get_name (| globals, locals_stack, "data" |);
                Constant.int 68;
                Constant.int 16
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, locals_stack, "t_0" |); M.get_name (| globals, locals_stack, "t_1" |) ],
            M.call (|
              M.get_name (| globals, locals_stack, "spit_le_to_uint" |),
              make_list [
                M.get_name (| globals, locals_stack, "data" |);
                Constant.int 196;
                Constant.int 2
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "f" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "Uint" |), "from_be_bytes" |),
              make_list [
                M.slice (|
                  M.get_name (| globals, locals_stack, "data" |),
                  Constant.int 212,
                  Constant.None_,
                  Constant.None_
                |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.return_ (|
            make_tuple [ M.get_name (| globals, locals_stack, "rounds" |); M.get_name (| globals, locals_stack, "h" |); M.get_name (| globals, locals_stack, "m" |); M.get_name (| globals, locals_stack, "t_0" |); M.get_name (| globals, locals_stack, "t_1" |); M.get_name (| globals, locals_stack, "f" |) ]
          |) in
          M.pure Constant.None_))
      );
      (
        "G",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "v"; "a"; "b"; "c"; "d"; "x"; "y" ] in
          ltac:(M.monadic (
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
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              M.get_name (| globals, locals_stack, "a" |)
            |),
            BinOp.mod_ (|
              BinOp.add (|
                BinOp.add (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "a" |)
                  |),
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "b" |)
                  |)
                |),
                M.get_name (| globals, locals_stack, "x" |)
              |),
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "max_word" |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              M.get_name (| globals, locals_stack, "d" |)
            |),
            BinOp.bit_xor (|
              BinOp.r_shift (|
                BinOp.bit_xor (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "d" |)
                  |),
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "a" |)
                  |)
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "R1" |)
              |),
              BinOp.mod_ (|
                BinOp.l_shift (|
                  BinOp.bit_xor (|
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "v" |),
                      M.get_name (| globals, locals_stack, "d" |)
                    |),
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "v" |),
                      M.get_name (| globals, locals_stack, "a" |)
                    |)
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "w_R1" |)
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "max_word" |)
              |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              M.get_name (| globals, locals_stack, "c" |)
            |),
            BinOp.mod_ (|
              BinOp.add (|
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "v" |),
                  M.get_name (| globals, locals_stack, "c" |)
                |),
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "v" |),
                  M.get_name (| globals, locals_stack, "d" |)
                |)
              |),
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "max_word" |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              M.get_name (| globals, locals_stack, "b" |)
            |),
            BinOp.bit_xor (|
              BinOp.r_shift (|
                BinOp.bit_xor (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "b" |)
                  |),
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "c" |)
                  |)
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "R2" |)
              |),
              BinOp.mod_ (|
                BinOp.l_shift (|
                  BinOp.bit_xor (|
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "v" |),
                      M.get_name (| globals, locals_stack, "b" |)
                    |),
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "v" |),
                      M.get_name (| globals, locals_stack, "c" |)
                    |)
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "w_R2" |)
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "max_word" |)
              |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              M.get_name (| globals, locals_stack, "a" |)
            |),
            BinOp.mod_ (|
              BinOp.add (|
                BinOp.add (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "a" |)
                  |),
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "b" |)
                  |)
                |),
                M.get_name (| globals, locals_stack, "y" |)
              |),
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "max_word" |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              M.get_name (| globals, locals_stack, "d" |)
            |),
            BinOp.bit_xor (|
              BinOp.r_shift (|
                BinOp.bit_xor (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "d" |)
                  |),
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "a" |)
                  |)
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "R3" |)
              |),
              BinOp.mod_ (|
                BinOp.l_shift (|
                  BinOp.bit_xor (|
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "v" |),
                      M.get_name (| globals, locals_stack, "d" |)
                    |),
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "v" |),
                      M.get_name (| globals, locals_stack, "a" |)
                    |)
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "w_R3" |)
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "max_word" |)
              |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              M.get_name (| globals, locals_stack, "c" |)
            |),
            BinOp.mod_ (|
              BinOp.add (|
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "v" |),
                  M.get_name (| globals, locals_stack, "c" |)
                |),
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "v" |),
                  M.get_name (| globals, locals_stack, "d" |)
                |)
              |),
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "max_word" |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              M.get_name (| globals, locals_stack, "b" |)
            |),
            BinOp.bit_xor (|
              BinOp.r_shift (|
                BinOp.bit_xor (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "b" |)
                  |),
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    M.get_name (| globals, locals_stack, "c" |)
                  |)
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "R4" |)
              |),
              BinOp.mod_ (|
                BinOp.l_shift (|
                  BinOp.bit_xor (|
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "v" |),
                      M.get_name (| globals, locals_stack, "b" |)
                    |),
                    M.get_subscript (|
                      M.get_name (| globals, locals_stack, "v" |),
                      M.get_name (| globals, locals_stack, "c" |)
                    |)
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "w_R4" |)
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "max_word" |)
              |)
            |)
          |) in
          let _ := M.return_ (|
            M.get_name (| globals, locals_stack, "v" |)
          |) in
          M.pure Constant.None_))
      );
      (
        "compress",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "num_rounds"; "h"; "m"; "t_0"; "t_1"; "f" ] in
          ltac:(M.monadic (
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
          let _ := M.assign_local (|
            "v" ,
            BinOp.mult (|
              make_list [
                Constant.int 0
              ],
              Constant.int 16
            |)
          |) in
          let _ := M.assign (|
            M.slice (|
              M.get_name (| globals, locals_stack, "v" |),
              Constant.int 0,
              Constant.int 8,
              Constant.None_
            |),
            M.get_name (| globals, locals_stack, "h" |)
          |) in
          let _ := M.assign (|
            M.slice (|
              M.get_name (| globals, locals_stack, "v" |),
              Constant.int 8,
              Constant.int 15,
              Constant.None_
            |),
            M.get_field (| M.get_name (| globals, locals_stack, "self" |), "IV" |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              Constant.int 12
            |),
            BinOp.bit_xor (|
              M.get_name (| globals, locals_stack, "t_0" |),
              M.get_subscript (|
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "IV" |),
                Constant.int 4
              |)
            |)
          |) in
          let _ := M.assign (|
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "v" |),
              Constant.int 13
            |),
            BinOp.bit_xor (|
              M.get_name (| globals, locals_stack, "t_1" |),
              M.get_subscript (|
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "IV" |),
                Constant.int 5
              |)
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              M.get_name (| globals, locals_stack, "f" |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.assign (|
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "v" |),
                  Constant.int 14
                |),
                BinOp.bit_xor (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "v" |),
                    Constant.int 14
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "mask_bits" |)
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, locals_stack, "r" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.get_name (| globals, locals_stack, "num_rounds" |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.assign_local (|
                  "s" ,
                  M.get_subscript (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "sigma" |),
                    BinOp.mod_ (|
                      M.get_name (| globals, locals_stack, "r" |),
                      M.get_field (| M.get_name (| globals, locals_stack, "self" |), "sigma_len" |)
                    |)
                  |)
                |) in
                let _ := M.assign_local (|
                  "v" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "G" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "v" |);
                      Constant.int 0;
                      Constant.int 4;
                      Constant.int 8;
                      Constant.int 12;
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 0
                        |)
                      |);
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 1
                        |)
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                let _ := M.assign_local (|
                  "v" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "G" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "v" |);
                      Constant.int 1;
                      Constant.int 5;
                      Constant.int 9;
                      Constant.int 13;
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 2
                        |)
                      |);
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 3
                        |)
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                let _ := M.assign_local (|
                  "v" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "G" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "v" |);
                      Constant.int 2;
                      Constant.int 6;
                      Constant.int 10;
                      Constant.int 14;
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 4
                        |)
                      |);
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 5
                        |)
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                let _ := M.assign_local (|
                  "v" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "G" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "v" |);
                      Constant.int 3;
                      Constant.int 7;
                      Constant.int 11;
                      Constant.int 15;
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 6
                        |)
                      |);
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 7
                        |)
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                let _ := M.assign_local (|
                  "v" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "G" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "v" |);
                      Constant.int 0;
                      Constant.int 5;
                      Constant.int 10;
                      Constant.int 15;
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 8
                        |)
                      |);
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 9
                        |)
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                let _ := M.assign_local (|
                  "v" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "G" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "v" |);
                      Constant.int 1;
                      Constant.int 6;
                      Constant.int 11;
                      Constant.int 12;
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 10
                        |)
                      |);
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 11
                        |)
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                let _ := M.assign_local (|
                  "v" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "G" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "v" |);
                      Constant.int 2;
                      Constant.int 7;
                      Constant.int 8;
                      Constant.int 13;
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 12
                        |)
                      |);
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 13
                        |)
                      |)
                    ],
                    make_dict []
                  |)
                |) in
                let _ := M.assign_local (|
                  "v" ,
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "G" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "v" |);
                      Constant.int 3;
                      Constant.int 4;
                      Constant.int 9;
                      Constant.int 14;
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 14
                        |)
                      |);
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "m" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "s" |),
                          Constant.int 15
                        |)
                      |)
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
          let _ := M.assign_local (|
            "result_message_words" ,
            Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
          |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "struct" |), "pack" |),
              make_list_concat (| [
                make_list [
                  BinOp.mod_ (|
                    Constant.str "<8%s",
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "word_format" |)
                  |)
                ];
                M.get_name (| globals, locals_stack, "result_message_words" |)
              ] |),
              make_dict []
            |)
          |) in
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
