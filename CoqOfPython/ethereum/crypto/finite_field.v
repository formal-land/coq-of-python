Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.crypto.finite_field".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Finite Fields
^^^^^^^^^^^^^
".

Axiom typing_imports_Iterable :
  IsImported globals "typing" "Iterable".
Axiom typing_imports_List :
  IsImported globals "typing" "List".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".
Axiom typing_imports_Type :
  IsImported globals "typing" "Type".
Axiom typing_imports_TypeVar :
  IsImported globals "typing" "TypeVar".
Axiom typing_imports_cast :
  IsImported globals "typing" "cast".

Axiom typing_extensions_imports_Protocol :
  IsImported globals "typing_extensions" "Protocol".

Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".
Axiom ethereum_base_types_imports_Bytes32 :
  IsImported globals "ethereum.base_types" "Bytes32".

Definition F : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "F"
    ],
    make_dict []
  |)
)).

Definition Field : Value.t :=
  builtins.make_klass
    [(globals, "Protocol")]
    [
      (
        "zero",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "from_int",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "n" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      )
    ]
    [
      (
        "__radd__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__iadd__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__sub__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__rsub__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__mul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__rmul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__imul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "exponent" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__ipow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__neg__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      );
      (
        "__truediv__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.ellipsis in
          M.pure Constant.None_))
      )
    ].

Definition T : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "T"
    ],
    make_dict []
  |)
)).

Definition PrimeField : Value.t :=
  builtins.make_klass
    [(globals, "int"); (globals, "Field")]
    [
      (
        "from_be_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "buffer" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts a sequence of bytes into a element of the field.
        Parameters
        ----------
        buffer :
            Bytes to decode.
        Returns
        -------
        self : `T`
            Unsigned integer decoded from `buffer`.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "cls" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "from_bytes" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "buffer" |);
                    Constant.str "big"
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "zero",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__new__" |),
              make_list [
                M.get_name (| globals, locals_stack, "cls" |);
                Constant.int 0
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "from_int",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "n" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "cls" |),
              make_list [
                M.get_name (| globals, locals_stack, "n" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ]
    [
      (
        "__new__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "value" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_name (| globals, locals_stack, "cls" |);
                BinOp.mod_ (|
                  M.get_name (| globals, locals_stack, "value" |),
                  M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "PRIME" |)
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__radd__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__add__" |),
              make_list [
                M.get_name (| globals, locals_stack, "left" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "right" |);
                  M.get_name (| globals, locals_stack, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, locals_stack, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__add__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |);
                    M.get_name (| globals, locals_stack, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__iadd__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__add__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__sub__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "right" |);
                  M.get_name (| globals, locals_stack, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, locals_stack, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__sub__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |);
                    M.get_name (| globals, locals_stack, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__rsub__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "left" |);
                  M.get_name (| globals, locals_stack, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, locals_stack, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rsub__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |);
                    M.get_name (| globals, locals_stack, "left" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__mul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "right" |);
                  M.get_name (| globals, locals_stack, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, locals_stack, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__mul__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |);
                    M.get_name (| globals, locals_stack, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__rmul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__mul__" |),
              make_list [
                M.get_name (| globals, locals_stack, "left" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__imul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__mul__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "exponent" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__pow__" |),
                  make_list [
                    M.call (|
                      M.get_name (| globals, locals_stack, "int" |),
                      make_list [
                        M.get_name (| globals, locals_stack, "self" |)
                      ],
                      make_dict []
                    |);
                    M.get_name (| globals, locals_stack, "exponent" |);
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "PRIME" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__ipow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__pow__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__neg__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__neg__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__truediv__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            BinOp.mult (|
              M.get_name (| globals, locals_stack, "self" |),
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "right" |), "multiplicative_inverse" |),
                make_list [],
                make_dict []
              |)
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "multiplicative_inverse",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            BinOp.pow (|
              M.get_name (| globals, locals_stack, "self" |),
              UnOp.sub (| Constant.int 1 |)
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "to_be_bytes32",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its big endian
        representation with exactly 32 bytes.
        Returns
        -------
        big_endian : `Bytes32`
            Big endian (most significant bits first) representation.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "Bytes32" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "to_bytes" |),
                  make_list [
                    Constant.int 32;
                    Constant.str "big"
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ].

Definition U : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "U"
    ],
    make_dict []
  |)
)).

Definition GaloisField : Value.t :=
  builtins.make_klass
    [(globals, "tuple"); (globals, "Field")]
    [
      (
        "zero",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__new__" |),
              make_list [
                M.get_name (| globals, locals_stack, "cls" |);
                BinOp.mult (|
                  make_list [
                    Constant.int 0
                  ],
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "MODULUS" |)
                    ],
                    make_dict []
                  |)
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "from_int",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "n" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__new__" |),
              make_list [
                M.get_name (| globals, locals_stack, "cls" |);
                BinOp.add (|
                  make_list [
                    M.get_name (| globals, locals_stack, "n" |)
                  ],
                  BinOp.mult (|
                    make_list [
                      Constant.int 0
                    ],
                    BinOp.sub (|
                      M.call (|
                        M.get_name (| globals, locals_stack, "len" |),
                        make_list [
                          M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "MODULUS" |)
                        ],
                        make_dict []
                      |),
                      Constant.int 1
                    |)
                  |)
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "calculate_frobenius_coefficients",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Calculate the coefficients needed by `frobenius()`.
        " in
          let _ := M.assign_local (|
            "coefficients" ,
            make_list []
          |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, locals_stack, "i" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "MODULUS" |)
          ],
          make_dict []
        |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.assign_local (|
                  "x" ,
                  BinOp.mult (|
                    make_list [
                      Constant.int 0
                    ],
                    M.call (|
                      M.get_name (| globals, locals_stack, "len" |),
                      make_list [
                        M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "MODULUS" |)
                      ],
                      make_dict []
                    |)
                  |)
                |) in
                let _ := M.assign (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "x" |),
                    M.get_name (| globals, locals_stack, "i" |)
                  |),
                  Constant.int 1
                |) in
                let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "coefficients" |), "append" |),
    make_list [
      BinOp.pow (|
        M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__new__" |),
          make_list [
            M.get_name (| globals, locals_stack, "cls" |);
            M.get_name (| globals, locals_stack, "x" |)
          ],
          make_dict []
        |),
        M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "PRIME" |)
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
            M.call (|
              M.get_name (| globals, locals_stack, "tuple" |),
              make_list [
                M.get_name (| globals, locals_stack, "coefficients" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ]
    [
      (
        "__new__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "iterable" ] in
          ltac:(M.monadic (
          let _ := M.assign_local (|
            "self" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "tuple" |), "__new__" |),
              make_list [
                M.get_name (| globals, locals_stack, "cls" |);
                Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
              ],
              make_dict []
            |)
          |) in
          let _ := M.assert (| Compare.eq (|
    M.call (|
      M.get_name (| globals, locals_stack, "len" |),
      make_list [
        M.get_name (| globals, locals_stack, "self" |)
      ],
      make_dict []
    |),
    M.call (|
      M.get_name (| globals, locals_stack, "len" |),
      make_list [
        M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "MODULUS" |)
      ],
      make_dict []
    |)
  |) |) in
          let _ := M.return_ (|
            M.get_name (| globals, locals_stack, "self" |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "right" |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "type" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |)
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, locals_stack, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__radd__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__add__" |),
              make_list [
                M.get_name (| globals, locals_stack, "left" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__iadd__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__add__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__sub__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "right" |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "type" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |)
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, locals_stack, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
(* At stmt: unsupported node type: AnnAssign *)
(* At stmt: unsupported node type: AnnAssign *)
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__rsub__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "left" |);
                  M.call (|
                    M.get_name (| globals, locals_stack, "type" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |)
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, locals_stack, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__mul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.assign_local (|
            "modulus" ,
            M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MODULUS" |)
          |) in
          let _ := M.assign_local (|
            "degree" ,
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                M.get_name (| globals, locals_stack, "modulus" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "prime" ,
            M.get_field (| M.get_name (| globals, locals_stack, "self" |), "PRIME" |)
          |) in
          let _ := M.assign_local (|
            "mul" ,
            BinOp.mult (|
              make_list [
                Constant.int 0
              ],
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "degree" |),
                Constant.int 2
              |)
            |)
          |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, locals_stack, "i" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.get_name (| globals, locals_stack, "degree" |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ :=
                  M.for_ (|
                    M.get_name (| globals, locals_stack, "j" |),
                    M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.get_name (| globals, locals_stack, "degree" |)
      ],
      make_dict []
    |),
                    ltac:(M.monadic (
                      let _ := M.assign_op (|
                        BinOp.add,
                        M.get_subscript (|
    M.get_name (| globals, locals_stack, "mul" |),
    BinOp.add (|
      M.get_name (| globals, locals_stack, "i" |),
      M.get_name (| globals, locals_stack, "j" |)
    |)
  |),
                        BinOp.mult (|
    M.get_subscript (|
      M.get_name (| globals, locals_stack, "self" |),
      M.get_name (| globals, locals_stack, "i" |)
    |),
    M.get_subscript (|
      M.get_name (| globals, locals_stack, "right" |),
      M.get_name (| globals, locals_stack, "j" |)
    |)
  |)
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
          let _ :=
            M.for_ (|
              M.get_name (| globals, locals_stack, "i" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        BinOp.sub (|
          BinOp.mult (|
            M.get_name (| globals, locals_stack, "degree" |),
            Constant.int 2
          |),
          Constant.int 1
        |);
        BinOp.sub (|
          M.get_name (| globals, locals_stack, "degree" |),
          Constant.int 1
        |);
        UnOp.sub (| Constant.int 1 |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ :=
                  M.for_ (|
                    M.get_name (| globals, locals_stack, "j" |),
                    M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        BinOp.sub (|
          M.get_name (| globals, locals_stack, "i" |),
          M.get_name (| globals, locals_stack, "degree" |)
        |);
        M.get_name (| globals, locals_stack, "i" |)
      ],
      make_dict []
    |),
                    ltac:(M.monadic (
                      let _ := M.assign_op (|
                        BinOp.sub,
                        M.get_subscript (|
    M.get_name (| globals, locals_stack, "mul" |),
    M.get_name (| globals, locals_stack, "j" |)
  |),
                        BinOp.mod_ (|
    BinOp.mult (|
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "mul" |),
        M.get_name (| globals, locals_stack, "i" |)
      |),
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "modulus" |),
        BinOp.sub (|
          M.get_name (| globals, locals_stack, "degree" |),
          BinOp.sub (|
            M.get_name (| globals, locals_stack, "i" |),
            M.get_name (| globals, locals_stack, "j" |)
          |)
        |)
      |)
    |),
    M.get_name (| globals, locals_stack, "prime" |)
  |)
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
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                M.slice (|
                  M.get_name (| globals, locals_stack, "mul" |),
                  Constant.None_,
                  M.get_name (| globals, locals_stack, "degree" |),
                  Constant.None_
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__rmul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__mul__" |),
              make_list [
                M.get_name (| globals, locals_stack, "left" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__imul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__mul__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__truediv__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            BinOp.mult (|
              M.get_name (| globals, locals_stack, "self" |),
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "right" |), "multiplicative_inverse" |),
                make_list [],
                make_dict []
              |)
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__neg__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "scalar_mul",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "x" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Multiply a field element by a integer. This is faster than using
        `from_int()` and field multiplication.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "deg",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        This is a support function for `multiplicative_inverse()`.
        " in
          let _ :=
            M.for_ (|
              M.get_name (| globals, locals_stack, "i" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MODULUS" |)
            ],
            make_dict []
          |),
          Constant.int 1
        |);
        UnOp.sub (| Constant.int 1 |);
        UnOp.sub (| Constant.int 1 |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.not_eq (|
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "self" |),
                        M.get_name (| globals, locals_stack, "i" |)
                      |),
                      Constant.int 0
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
          let _ := M.raise (| Some (M.call (|
            M.get_name (| globals, locals_stack, "ValueError" |),
            make_list [
              Constant.str "deg() does not support zero"
            ],
            make_dict []
          |)) |) in
          M.pure Constant.None_))
      );
      (
        "multiplicative_inverse",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Calculate the multiplicative inverse. Uses the Euclidean algorithm.
        " in
(* At stmt: unsupported node type: AnnAssign *)
          let _ := M.assign_local (|
            "p" ,
            M.get_field (| M.get_name (| globals, locals_stack, "self" |), "PRIME" |)
          |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, locals_stack, "x1" |); M.get_name (| globals, locals_stack, "f1" |) ],
            make_tuple [ M.call (|
              M.get_name (| globals, locals_stack, "list" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MODULUS" |)
              ],
              make_dict []
            |); BinOp.mult (|
              make_list [
                Constant.int 0
              ],
              M.call (|
                M.get_name (| globals, locals_stack, "len" |),
                make_list [
                  M.get_name (| globals, locals_stack, "self" |)
                ],
                make_dict []
              |)
            |) ]
          |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, locals_stack, "x2" |); M.get_name (| globals, locals_stack, "f2" |); M.get_name (| globals, locals_stack, "d2" |) ],
            make_tuple [ M.call (|
              M.get_name (| globals, locals_stack, "list" |),
              make_list [
                M.get_name (| globals, locals_stack, "self" |)
              ],
              make_dict []
            |); BinOp.add (|
              make_list [
                Constant.int 1
              ],
              BinOp.mult (|
                make_list [
                  Constant.int 0
                ],
                BinOp.sub (|
                  M.call (|
                    M.get_name (| globals, locals_stack, "len" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |)
                    ],
                    make_dict []
                  |),
                  Constant.int 1
                |)
              |)
            |); M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "deg" |),
              make_list [],
              make_dict []
            |) ]
          |) in
          let _ := M.assign_local (|
            "q_0" ,
            M.call (|
              M.get_name (| globals, locals_stack, "pow" |),
              make_list [
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "x2" |),
                  M.get_name (| globals, locals_stack, "d2" |)
                |);
                UnOp.sub (| Constant.int 1 |);
                M.get_name (| globals, locals_stack, "p" |)
              ],
              make_dict []
            |)
          |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, locals_stack, "i" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.get_name (| globals, locals_stack, "d2" |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.assign (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "x1" |),
                    BinOp.sub (|
                      BinOp.add (|
                        M.get_name (| globals, locals_stack, "i" |),
                        M.call (|
                          M.get_name (| globals, locals_stack, "len" |),
                          make_list [
                            M.get_name (| globals, locals_stack, "x1" |)
                          ],
                          make_dict []
                        |)
                      |),
                      M.get_name (| globals, locals_stack, "d2" |)
                    |)
                  |),
                  BinOp.mod_ (|
                    BinOp.sub (|
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "x1" |),
                        BinOp.sub (|
                          BinOp.add (|
                            M.get_name (| globals, locals_stack, "i" |),
                            M.call (|
                              M.get_name (| globals, locals_stack, "len" |),
                              make_list [
                                M.get_name (| globals, locals_stack, "x1" |)
                              ],
                              make_dict []
                            |)
                          |),
                          M.get_name (| globals, locals_stack, "d2" |)
                        |)
                      |),
                      BinOp.mult (|
                        M.get_name (| globals, locals_stack, "q_0" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "x2" |),
                          M.get_name (| globals, locals_stack, "i" |)
                        |)
                      |)
                    |),
                    M.get_name (| globals, locals_stack, "p" |)
                  |)
                |) in
                let _ := M.assign (|
                  M.get_subscript (|
                    M.get_name (| globals, locals_stack, "f1" |),
                    BinOp.sub (|
                      BinOp.add (|
                        M.get_name (| globals, locals_stack, "i" |),
                        M.call (|
                          M.get_name (| globals, locals_stack, "len" |),
                          make_list [
                            M.get_name (| globals, locals_stack, "x1" |)
                          ],
                          make_dict []
                        |)
                      |),
                      M.get_name (| globals, locals_stack, "d2" |)
                    |)
                  |),
                  BinOp.mod_ (|
                    BinOp.sub (|
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "f1" |),
                        BinOp.sub (|
                          BinOp.add (|
                            M.get_name (| globals, locals_stack, "i" |),
                            M.call (|
                              M.get_name (| globals, locals_stack, "len" |),
                              make_list [
                                M.get_name (| globals, locals_stack, "x1" |)
                              ],
                              make_dict []
                            |)
                          |),
                          M.get_name (| globals, locals_stack, "d2" |)
                        |)
                      |),
                      BinOp.mult (|
                        M.get_name (| globals, locals_stack, "q_0" |),
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "f2" |),
                          M.get_name (| globals, locals_stack, "i" |)
                        |)
                      |)
                    |),
                    M.get_name (| globals, locals_stack, "p" |)
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
              M.get_name (| globals, locals_stack, "i" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MODULUS" |)
            ],
            make_dict []
          |),
          Constant.int 1
        |);
        UnOp.sub (| Constant.int 1 |);
        UnOp.sub (| Constant.int 1 |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.not_eq (|
                      M.get_subscript (|
                        M.get_name (| globals, locals_stack, "x1" |),
                        M.get_name (| globals, locals_stack, "i" |)
                      |),
                      Constant.int 0
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.assign_local (|
                      "d1" ,
                      M.get_name (| globals, locals_stack, "i" |)
                    |) in
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
            M.while (|
              Constant.bool true,
              ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.eq (|
                      M.get_name (| globals, locals_stack, "d1" |),
                      Constant.int 0
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.assign_local (|
                      "ans" ,
                      M.get_name (| globals, locals_stack, "f1" |)
                    |) in
                    let _ := M.assign_local (|
                      "q" ,
                      M.call (|
                        M.get_name (| globals, locals_stack, "pow" |),
                        make_list [
                          M.get_subscript (|
                            M.get_name (| globals, locals_stack, "x1" |),
                            Constant.int 0
                          |);
                          UnOp.sub (| Constant.int 1 |);
                          M.get_field (| M.get_name (| globals, locals_stack, "self" |), "PRIME" |)
                        ],
                        make_dict []
                      |)
                    |) in
                    let _ :=
                      M.for_ (|
                        M.get_name (| globals, locals_stack, "i" |),
                        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_name (| globals, locals_stack, "ans" |)
          ],
          make_dict []
        |)
      ],
      make_dict []
    |),
                        ltac:(M.monadic (
                          let _ := M.assign_op (|
                            BinOp.mult,
                            M.get_subscript (|
    M.get_name (| globals, locals_stack, "ans" |),
    M.get_name (| globals, locals_stack, "i" |)
  |),
                            M.get_name (| globals, locals_stack, "q" |)
                          |) in
                          M.pure Constant.None_
                        )),
                        ltac:(M.monadic (
                          M.pure Constant.None_
                        ))
                    |) in
                    let _ := M.break (| |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    let _ :=
                      (* if *)
                      M.if_then_else (|
                        Compare.eq (|
                          M.get_name (| globals, locals_stack, "d2" |),
                          Constant.int 0
                        |),
                      (* then *)
                      ltac:(M.monadic (
                        let _ := M.assign_local (|
                          "ans" ,
                          M.get_name (| globals, locals_stack, "f2" |)
                        |) in
                        let _ := M.assign_local (|
                          "q" ,
                          M.call (|
                            M.get_name (| globals, locals_stack, "pow" |),
                            make_list [
                              M.get_subscript (|
                                M.get_name (| globals, locals_stack, "x2" |),
                                Constant.int 0
                              |);
                              UnOp.sub (| Constant.int 1 |);
                              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "PRIME" |)
                            ],
                            make_dict []
                          |)
                        |) in
                        let _ :=
                          M.for_ (|
                            M.get_name (| globals, locals_stack, "i" |),
                            M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        M.call (|
          M.get_name (| globals, locals_stack, "len" |),
          make_list [
            M.get_name (| globals, locals_stack, "ans" |)
          ],
          make_dict []
        |)
      ],
      make_dict []
    |),
                            ltac:(M.monadic (
                              let _ := M.assign_op_local (|
                                BinOp.mult,
                                "ans",
                                M.get_name (| globals, locals_stack, "q" |)
                              |) in
                              M.pure Constant.None_
                            )),
                            ltac:(M.monadic (
                              M.pure Constant.None_
                            ))
                        |) in
                        let _ := M.break (| |) in
                        M.pure Constant.None_
                      (* else *)
                      )), ltac:(M.monadic (
                        M.pure Constant.None_
                      )) |) in
                    M.pure Constant.None_
                  )) |) in
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.lt (|
                      M.get_name (| globals, locals_stack, "d1" |),
                      M.get_name (| globals, locals_stack, "d2" |)
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.assign_local (|
                      "q" ,
                      BinOp.mult (|
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "x2" |),
                          M.get_name (| globals, locals_stack, "d2" |)
                        |),
                        M.call (|
                          M.get_name (| globals, locals_stack, "pow" |),
                          make_list [
                            M.get_subscript (|
                              M.get_name (| globals, locals_stack, "x1" |),
                              M.get_name (| globals, locals_stack, "d1" |)
                            |);
                            UnOp.sub (| Constant.int 1 |);
                            M.get_field (| M.get_name (| globals, locals_stack, "self" |), "PRIME" |)
                          ],
                          make_dict []
                        |)
                      |)
                    |) in
                    let _ :=
                      M.for_ (|
                        M.get_name (| globals, locals_stack, "i" |),
                        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MODULUS" |)
            ],
            make_dict []
          |),
          BinOp.sub (|
            M.get_name (| globals, locals_stack, "d2" |),
            M.get_name (| globals, locals_stack, "d1" |)
          |)
        |)
      ],
      make_dict []
    |),
                        ltac:(M.monadic (
                          let _ := M.assign (|
                            M.get_subscript (|
                              M.get_name (| globals, locals_stack, "x2" |),
                              BinOp.add (|
                                M.get_name (| globals, locals_stack, "i" |),
                                BinOp.sub (|
                                  M.get_name (| globals, locals_stack, "d2" |),
                                  M.get_name (| globals, locals_stack, "d1" |)
                                |)
                              |)
                            |),
                            BinOp.mod_ (|
                              BinOp.sub (|
                                M.get_subscript (|
                                  M.get_name (| globals, locals_stack, "x2" |),
                                  BinOp.add (|
                                    M.get_name (| globals, locals_stack, "i" |),
                                    BinOp.sub (|
                                      M.get_name (| globals, locals_stack, "d2" |),
                                      M.get_name (| globals, locals_stack, "d1" |)
                                    |)
                                  |)
                                |),
                                BinOp.mult (|
                                  M.get_name (| globals, locals_stack, "q" |),
                                  M.get_subscript (|
                                    M.get_name (| globals, locals_stack, "x1" |),
                                    M.get_name (| globals, locals_stack, "i" |)
                                  |)
                                |)
                              |),
                              M.get_name (| globals, locals_stack, "p" |)
                            |)
                          |) in
                          let _ := M.assign (|
                            M.get_subscript (|
                              M.get_name (| globals, locals_stack, "f2" |),
                              BinOp.add (|
                                M.get_name (| globals, locals_stack, "i" |),
                                BinOp.sub (|
                                  M.get_name (| globals, locals_stack, "d2" |),
                                  M.get_name (| globals, locals_stack, "d1" |)
                                |)
                              |)
                            |),
                            BinOp.mod_ (|
                              BinOp.sub (|
                                M.get_subscript (|
                                  M.get_name (| globals, locals_stack, "f2" |),
                                  BinOp.add (|
                                    M.get_name (| globals, locals_stack, "i" |),
                                    BinOp.sub (|
                                      M.get_name (| globals, locals_stack, "d2" |),
                                      M.get_name (| globals, locals_stack, "d1" |)
                                    |)
                                  |)
                                |),
                                BinOp.mult (|
                                  M.get_name (| globals, locals_stack, "q" |),
                                  M.get_subscript (|
                                    M.get_name (| globals, locals_stack, "f1" |),
                                    M.get_name (| globals, locals_stack, "i" |)
                                  |)
                                |)
                              |),
                              M.get_name (| globals, locals_stack, "p" |)
                            |)
                          |) in
                          M.pure Constant.None_
                        )),
                        ltac:(M.monadic (
                          M.pure Constant.None_
                        ))
                    |) in
                    let _ :=
                      M.while (|
                        Compare.eq (|
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "x2" |),
        M.get_name (| globals, locals_stack, "d2" |)
      |),
      Constant.int 0
    |),
                        ltac:(M.monadic (
                          let _ := M.assign_op_local (|
                            BinOp.sub,
                            "d2",
                            Constant.int 1
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
                    let _ := M.assign_local (|
                      "q" ,
                      BinOp.mult (|
                        M.get_subscript (|
                          M.get_name (| globals, locals_stack, "x1" |),
                          M.get_name (| globals, locals_stack, "d1" |)
                        |),
                        M.call (|
                          M.get_name (| globals, locals_stack, "pow" |),
                          make_list [
                            M.get_subscript (|
                              M.get_name (| globals, locals_stack, "x2" |),
                              M.get_name (| globals, locals_stack, "d2" |)
                            |);
                            UnOp.sub (| Constant.int 1 |);
                            M.get_field (| M.get_name (| globals, locals_stack, "self" |), "PRIME" |)
                          ],
                          make_dict []
                        |)
                      |)
                    |) in
                    let _ :=
                      M.for_ (|
                        M.get_name (| globals, locals_stack, "i" |),
                        M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MODULUS" |)
            ],
            make_dict []
          |),
          BinOp.sub (|
            M.get_name (| globals, locals_stack, "d1" |),
            M.get_name (| globals, locals_stack, "d2" |)
          |)
        |)
      ],
      make_dict []
    |),
                        ltac:(M.monadic (
                          let _ := M.assign (|
                            M.get_subscript (|
                              M.get_name (| globals, locals_stack, "x1" |),
                              BinOp.add (|
                                M.get_name (| globals, locals_stack, "i" |),
                                BinOp.sub (|
                                  M.get_name (| globals, locals_stack, "d1" |),
                                  M.get_name (| globals, locals_stack, "d2" |)
                                |)
                              |)
                            |),
                            BinOp.mod_ (|
                              BinOp.sub (|
                                M.get_subscript (|
                                  M.get_name (| globals, locals_stack, "x1" |),
                                  BinOp.add (|
                                    M.get_name (| globals, locals_stack, "i" |),
                                    BinOp.sub (|
                                      M.get_name (| globals, locals_stack, "d1" |),
                                      M.get_name (| globals, locals_stack, "d2" |)
                                    |)
                                  |)
                                |),
                                BinOp.mult (|
                                  M.get_name (| globals, locals_stack, "q" |),
                                  M.get_subscript (|
                                    M.get_name (| globals, locals_stack, "x2" |),
                                    M.get_name (| globals, locals_stack, "i" |)
                                  |)
                                |)
                              |),
                              M.get_name (| globals, locals_stack, "p" |)
                            |)
                          |) in
                          let _ := M.assign (|
                            M.get_subscript (|
                              M.get_name (| globals, locals_stack, "f1" |),
                              BinOp.add (|
                                M.get_name (| globals, locals_stack, "i" |),
                                BinOp.sub (|
                                  M.get_name (| globals, locals_stack, "d1" |),
                                  M.get_name (| globals, locals_stack, "d2" |)
                                |)
                              |)
                            |),
                            BinOp.mod_ (|
                              BinOp.sub (|
                                M.get_subscript (|
                                  M.get_name (| globals, locals_stack, "f1" |),
                                  BinOp.add (|
                                    M.get_name (| globals, locals_stack, "i" |),
                                    BinOp.sub (|
                                      M.get_name (| globals, locals_stack, "d1" |),
                                      M.get_name (| globals, locals_stack, "d2" |)
                                    |)
                                  |)
                                |),
                                BinOp.mult (|
                                  M.get_name (| globals, locals_stack, "q" |),
                                  M.get_subscript (|
                                    M.get_name (| globals, locals_stack, "f2" |),
                                    M.get_name (| globals, locals_stack, "i" |)
                                  |)
                                |)
                              |),
                              M.get_name (| globals, locals_stack, "p" |)
                            |)
                          |) in
                          M.pure Constant.None_
                        )),
                        ltac:(M.monadic (
                          M.pure Constant.None_
                        ))
                    |) in
                    let _ :=
                      M.while (|
                        Compare.eq (|
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "x1" |),
        M.get_name (| globals, locals_stack, "d1" |)
      |),
      Constant.int 0
    |),
                        ltac:(M.monadic (
                          let _ := M.assign_op_local (|
                            BinOp.sub,
                            "d1",
                            Constant.int 1
                          |) in
                          M.pure Constant.None_
                        )),
                        ltac:(M.monadic (
                          M.pure Constant.None_
                        ))
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
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                M.get_name (| globals, locals_stack, "ans" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "exponent" ] in
          ltac:(M.monadic (
          let _ := M.assign_local (|
            "degree" ,
            M.call (|
              M.get_name (| globals, locals_stack, "len" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MODULUS" |)
              ],
              make_dict []
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "exponent" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.assign_local (|
                "self" ,
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "multiplicative_inverse" |),
                  make_list [],
                  make_dict []
                |)
              |) in
              let _ := M.assign_local (|
                "exponent" ,
                UnOp.sub (| M.get_name (| globals, locals_stack, "exponent" |) |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_local (|
            "res" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, locals_stack, "type" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |);
                BinOp.add (|
                  make_list [
                    Constant.int 1
                  ],
                  BinOp.mult (|
                    make_list [
                      Constant.int 0
                    ],
                    BinOp.sub (|
                      M.get_name (| globals, locals_stack, "degree" |),
                      Constant.int 1
                    |)
                  |)
                |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "s" ,
            M.get_name (| globals, locals_stack, "self" |)
          |) in
          let _ :=
            M.while (|
              Compare.not_eq (|
      M.get_name (| globals, locals_stack, "exponent" |),
      Constant.int 0
    |),
              ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.eq (|
                      BinOp.mod_ (|
                        M.get_name (| globals, locals_stack, "exponent" |),
                        Constant.int 2
                      |),
                      Constant.int 1
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.assign_op_local (|
                      BinOp.mult,
                      "res",
                      M.get_name (| globals, locals_stack, "s" |)
                    |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    M.pure Constant.None_
                  )) |) in
                let _ := M.assign_op_local (|
                  BinOp.mult,
                  "s",
                  M.get_name (| globals, locals_stack, "s" |)
                |) in
                let _ := M.assign_op_local (|
                  BinOp.floor_div,
                  "exponent",
                  Constant.int 2
                |) in
                M.pure Constant.None_
              )),
              ltac:(M.monadic (
                M.pure Constant.None_
              ))
          |) in
          let _ := M.return_ (|
            M.get_name (| globals, locals_stack, "res" |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__ipow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__pow__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "frobenius",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Returns `self ** p`. This function is known as the Frobenius
        endomorphism and has many special mathematical properties. In
        particular it is extremely cheap to compute compared to other
        exponentiations.
        " in
          let _ := M.assign_local (|
            "ans" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "from_int" |),
              make_list [
                Constant.int 0
              ],
              make_dict []
            |)
          |) in
(* At stmt: unsupported node type: AnnAssign *)
          let _ :=
            M.for_ (|
              make_tuple [ M.get_name (| globals, locals_stack, "i" |); M.get_name (| globals, locals_stack, "a" |) ],
              M.call (|
      M.get_name (| globals, locals_stack, "enumerate" |),
      make_list [
        M.get_name (| globals, locals_stack, "self" |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.assign_op_local (|
                  BinOp.add,
                  "ans",
                  M.call (|
    M.get_field (| M.call (|
      M.get_name (| globals, locals_stack, "cast" |),
      make_list [
        M.get_name (| globals, locals_stack, "U" |);
        M.get_subscript (|
          M.get_field (| M.get_name (| globals, locals_stack, "self" |), "FROBENIUS_COEFFICIENTS" |),
          M.get_name (| globals, locals_stack, "i" |)
        |)
      ],
      make_dict []
    |), "scalar_mul" |),
    make_list [
      M.get_name (| globals, locals_stack, "a" |)
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
          let _ := M.return_ (|
            M.get_name (| globals, locals_stack, "ans" |)
          |) in
          M.pure Constant.None_))
      )
    ].
