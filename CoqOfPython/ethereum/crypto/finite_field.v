Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.crypto.finite_field".

Definition expr_1 : Value.t :=
  Constant.str "
Finite Fields
^^^^^^^^^^^^^
".

Axiom typing_imports :
  AreImported globals "typing" [ "Iterable"; "List"; "Tuple"; "Type"; "TypeVar"; "cast" ].

Axiom typing_extensions_imports :
  AreImported globals "typing_extensions" [ "Protocol" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "Bytes"; "Bytes32" ].

Definition F : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "from_int",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "n" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      )
    ]
    [
      (
        "__radd__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__iadd__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__sub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__rsub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__mul__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__rmul__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__imul__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "exponent" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__ipow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__neg__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      );
      (
        "__truediv__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := (* At constant: unsupported node type: Constant *) in
          M.pure Constant.None_))
      )
    ].

Definition T : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "buffer" ] |) in
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
              M.get_name (| globals, "cls" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |),
                  make_list [
                    M.get_name (| globals, "buffer" |);
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "cls" |), "__new__" |),
              make_list [
                M.get_name (| globals, "cls" |);
                Constant.int 0
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "from_int",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "n" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "cls" |),
              make_list [
                M.get_name (| globals, "n" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "value" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_name (| globals, "cls" |);
                BinOp.mod_ (|
                  M.get_name (| globals, "value" |),
                  M.get_field (| M.get_name (| globals, "cls" |), "PRIME" |)
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__radd__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__add__" |),
              make_list [
                M.get_name (| globals, "left" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "right" |);
                  M.get_name (| globals, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__add__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__add__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__sub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "right" |);
                  M.get_name (| globals, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__sub__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "left" |);
                  M.get_name (| globals, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rsub__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "right" |);
                  M.get_name (| globals, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__mul__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__mul__" |),
              make_list [
                M.get_name (| globals, "left" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__imul__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__mul__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "exponent" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__pow__" |),
                  make_list [
                    M.call (|
                      M.get_name (| globals, "int" |),
                      make_list [
                        M.get_name (| globals, "self" |)
                      ],
                      make_dict []
                    |);
                    M.get_name (| globals, "exponent" |);
                    M.get_field (| M.get_name (| globals, "self" |), "PRIME" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__pow__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__neg__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
                  ],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__neg__" |),
                  make_list [
                    M.get_name (| globals, "self" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            BinOp.mult (|
              M.get_name (| globals, "self" |),
              M.call (|
                M.get_field (| M.get_name (| globals, "right" |), "multiplicative_inverse" |),
                make_list [],
                make_dict []
              |)
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "multiplicative_inverse",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := M.return_ (|
            BinOp.pow (|
              M.get_name (| globals, "self" |),
              UnOp.sub (| Constant.int 1 |)
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "to_be_bytes32",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
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
              M.get_name (| globals, "Bytes32" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |),
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
    M.get_name (| globals, "TypeVar" |),
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "cls" |), "__new__" |),
              make_list [
                M.get_name (| globals, "cls" |);
                BinOp.mult (|
                  make_list [
                    Constant.int 0
                  ],
                  M.call (|
                    M.get_name (| globals, "len" |),
                    make_list [
                      M.get_field (| M.get_name (| globals, "cls" |), "MODULUS" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "n" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "cls" |), "__new__" |),
              make_list [
                M.get_name (| globals, "cls" |);
                BinOp.add (|
                  make_list [
                    M.get_name (| globals, "n" |)
                  ],
                  BinOp.mult (|
                    make_list [
                      Constant.int 0
                    ],
                    BinOp.sub (|
                      M.call (|
                        M.get_name (| globals, "len" |),
                        make_list [
                          M.get_field (| M.get_name (| globals, "cls" |), "MODULUS" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls" ] |) in
          let _ := Constant.str "
        Calculate the coefficients needed by `frobenius()`.
        " in
          let coefficients :=
            make_list [] in
          let _ :=
            M.for_ (|
              M.get_name (| globals, "i" |),
              M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_field (| M.get_name (| globals, "cls" |), "MODULUS" |)
          ],
          make_dict []
        |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let x :=
                  BinOp.mult (|
                    make_list [
                      Constant.int 0
                    ],
                    M.call (|
                      M.get_name (| globals, "len" |),
                      make_list [
                        M.get_field (| M.get_name (| globals, "cls" |), "MODULUS" |)
                      ],
                      make_dict []
                    |)
                  |) in
                let _ := M.assign (|
                  M.get_subscript (|
                    M.get_name (| globals, "x" |),
                    M.get_name (| globals, "i" |)
                  |),
                  Constant.int 1
                |) in
                let _ := M.call (|
    M.get_field (| M.get_name (| globals, "coefficients" |), "append" |),
    make_list [
      BinOp.pow (|
        M.call (|
          M.get_field (| M.get_name (| globals, "cls" |), "__new__" |),
          make_list [
            M.get_name (| globals, "cls" |);
            M.get_name (| globals, "x" |)
          ],
          make_dict []
        |),
        M.get_field (| M.get_name (| globals, "cls" |), "PRIME" |)
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
              M.get_name (| globals, "tuple" |),
              make_list [
                M.get_name (| globals, "coefficients" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "iterable" ] |) in
          let self :=
            M.call (|
              M.get_field (| M.get_name (| globals, "tuple" |), "__new__" |),
              make_list [
                M.get_name (| globals, "cls" |);
                Constant.str "(* At expr: unsupported node type: GeneratorExp *)"
              ],
              make_dict []
            |) in
          let _ := M.assert (| Compare.eq (|
    M.call (|
      M.get_name (| globals, "len" |),
      make_list [
        M.get_name (| globals, "self" |)
      ],
      make_dict []
    |),
    M.call (|
      M.get_name (| globals, "len" |),
      make_list [
        M.get_field (| M.get_name (| globals, "cls" |), "MODULUS" |)
      ],
      make_dict []
    |)
  |) |) in
          let _ := M.return_ (|
            M.get_name (| globals, "self" |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "right" |);
                  M.call (|
                    M.get_name (| globals, "type" |),
                    make_list [
                      M.get_name (| globals, "self" |)
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__add__" |),
              make_list [
                M.get_name (| globals, "left" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__iadd__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__add__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__sub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "right" |);
                  M.call (|
                    M.get_name (| globals, "type" |),
                    make_list [
                      M.get_name (| globals, "self" |)
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, "NotImplemented" |)
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
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "left" |);
                  M.call (|
                    M.get_name (| globals, "type" |),
                    make_list [
                      M.get_name (| globals, "self" |)
                    ],
                    make_dict []
                  |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.get_name (| globals, "NotImplemented" |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let modulus :=
            M.get_field (| M.get_name (| globals, "self" |), "MODULUS" |) in
          let degree :=
            M.call (|
              M.get_name (| globals, "len" |),
              make_list [
                M.get_name (| globals, "modulus" |)
              ],
              make_dict []
            |) in
          let prime :=
            M.get_field (| M.get_name (| globals, "self" |), "PRIME" |) in
          let mul :=
            BinOp.mult (|
              make_list [
                Constant.int 0
              ],
              BinOp.mult (|
                M.get_name (| globals, "degree" |),
                Constant.int 2
              |)
            |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, "i" |),
              M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        M.get_name (| globals, "degree" |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ :=
                  M.for_ (|
                    M.get_name (| globals, "j" |),
                    M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        M.get_name (| globals, "degree" |)
      ],
      make_dict []
    |),
                    ltac:(M.monadic (
                      let _ := M.assign_op (|
                        BinOp.add,
                        M.get_subscript (|
    M.get_name (| globals, "mul" |),
    BinOp.add (|
      M.get_name (| globals, "i" |),
      M.get_name (| globals, "j" |)
    |)
  |),
                        BinOp.mult (|
    M.get_subscript (|
      M.get_name (| globals, "self" |),
      M.get_name (| globals, "i" |)
    |),
    M.get_subscript (|
      M.get_name (| globals, "right" |),
      M.get_name (| globals, "j" |)
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
              M.get_name (| globals, "i" |),
              M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        BinOp.sub (|
          BinOp.mult (|
            M.get_name (| globals, "degree" |),
            Constant.int 2
          |),
          Constant.int 1
        |);
        BinOp.sub (|
          M.get_name (| globals, "degree" |),
          Constant.int 1
        |);
        UnOp.sub (| Constant.int 1 |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ :=
                  M.for_ (|
                    M.get_name (| globals, "j" |),
                    M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        BinOp.sub (|
          M.get_name (| globals, "i" |),
          M.get_name (| globals, "degree" |)
        |);
        M.get_name (| globals, "i" |)
      ],
      make_dict []
    |),
                    ltac:(M.monadic (
                      let _ := M.assign_op (|
                        BinOp.sub,
                        M.get_subscript (|
    M.get_name (| globals, "mul" |),
    M.get_name (| globals, "j" |)
  |),
                        BinOp.mod_ (|
    BinOp.mult (|
      M.get_subscript (|
        M.get_name (| globals, "mul" |),
        M.get_name (| globals, "i" |)
      |),
      M.get_subscript (|
        M.get_name (| globals, "modulus" |),
        BinOp.sub (|
          M.get_name (| globals, "degree" |),
          BinOp.sub (|
            M.get_name (| globals, "i" |),
            M.get_name (| globals, "j" |)
          |)
        |)
      |)
    |),
    M.get_name (| globals, "prime" |)
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
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
                  ],
                  make_dict []
                |);
                M.slice (|
                  M.get_name (| globals, "mul" |),
                  Constant.None_,
                  M.get_name (| globals, "degree" |),
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__mul__" |),
              make_list [
                M.get_name (| globals, "left" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__imul__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__mul__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__truediv__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            BinOp.mult (|
              M.get_name (| globals, "self" |),
              M.call (|
                M.get_field (| M.get_name (| globals, "right" |), "multiplicative_inverse" |),
                make_list [],
                make_dict []
              |)
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__neg__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "x" ] |) in
          let _ := Constant.str "
        Multiply a field element by a integer. This is faster than using
        `from_int()` and field multiplication.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        This is a support function for `multiplicative_inverse()`.
        " in
          let _ :=
            M.for_ (|
              M.get_name (| globals, "i" |),
              M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, "self" |), "MODULUS" |)
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
                        M.get_name (| globals, "self" |),
                        M.get_name (| globals, "i" |)
                      |),
                      Constant.int 0
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let _ := M.return_ (|
                      M.get_name (| globals, "i" |)
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
            M.get_name (| globals, "ValueError" |),
            make_list [
              Constant.str "deg() does not support zero"
            ],
            make_dict []
          |)) |) in
          M.pure Constant.None_))
      );
      (
        "multiplicative_inverse",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Calculate the multiplicative inverse. Uses the Euclidean algorithm.
        " in
(* At stmt: unsupported node type: AnnAssign *)
          let p :=
            M.get_field (| M.get_name (| globals, "self" |), "PRIME" |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, "x1" |); M.get_name (| globals, "f1" |) ],
            make_tuple [ M.call (|
              M.get_name (| globals, "list" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "MODULUS" |)
              ],
              make_dict []
            |); BinOp.mult (|
              make_list [
                Constant.int 0
              ],
              M.call (|
                M.get_name (| globals, "len" |),
                make_list [
                  M.get_name (| globals, "self" |)
                ],
                make_dict []
              |)
            |) ]
          |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, "x2" |); M.get_name (| globals, "f2" |); M.get_name (| globals, "d2" |) ],
            make_tuple [ M.call (|
              M.get_name (| globals, "list" |),
              make_list [
                M.get_name (| globals, "self" |)
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
                    M.get_name (| globals, "len" |),
                    make_list [
                      M.get_name (| globals, "self" |)
                    ],
                    make_dict []
                  |),
                  Constant.int 1
                |)
              |)
            |); M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "deg" |),
              make_list [],
              make_dict []
            |) ]
          |) in
          let q_0 :=
            M.call (|
              M.get_name (| globals, "pow" |),
              make_list [
                M.get_subscript (|
                  M.get_name (| globals, "x2" |),
                  M.get_name (| globals, "d2" |)
                |);
                UnOp.sub (| Constant.int 1 |);
                M.get_name (| globals, "p" |)
              ],
              make_dict []
            |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, "i" |),
              M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        M.get_name (| globals, "d2" |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.assign (|
                  M.get_subscript (|
                    M.get_name (| globals, "x1" |),
                    BinOp.sub (|
                      BinOp.add (|
                        M.get_name (| globals, "i" |),
                        M.call (|
                          M.get_name (| globals, "len" |),
                          make_list [
                            M.get_name (| globals, "x1" |)
                          ],
                          make_dict []
                        |)
                      |),
                      M.get_name (| globals, "d2" |)
                    |)
                  |),
                  BinOp.mod_ (|
                    BinOp.sub (|
                      M.get_subscript (|
                        M.get_name (| globals, "x1" |),
                        BinOp.sub (|
                          BinOp.add (|
                            M.get_name (| globals, "i" |),
                            M.call (|
                              M.get_name (| globals, "len" |),
                              make_list [
                                M.get_name (| globals, "x1" |)
                              ],
                              make_dict []
                            |)
                          |),
                          M.get_name (| globals, "d2" |)
                        |)
                      |),
                      BinOp.mult (|
                        M.get_name (| globals, "q_0" |),
                        M.get_subscript (|
                          M.get_name (| globals, "x2" |),
                          M.get_name (| globals, "i" |)
                        |)
                      |)
                    |),
                    M.get_name (| globals, "p" |)
                  |)
                |) in
                let _ := M.assign (|
                  M.get_subscript (|
                    M.get_name (| globals, "f1" |),
                    BinOp.sub (|
                      BinOp.add (|
                        M.get_name (| globals, "i" |),
                        M.call (|
                          M.get_name (| globals, "len" |),
                          make_list [
                            M.get_name (| globals, "x1" |)
                          ],
                          make_dict []
                        |)
                      |),
                      M.get_name (| globals, "d2" |)
                    |)
                  |),
                  BinOp.mod_ (|
                    BinOp.sub (|
                      M.get_subscript (|
                        M.get_name (| globals, "f1" |),
                        BinOp.sub (|
                          BinOp.add (|
                            M.get_name (| globals, "i" |),
                            M.call (|
                              M.get_name (| globals, "len" |),
                              make_list [
                                M.get_name (| globals, "x1" |)
                              ],
                              make_dict []
                            |)
                          |),
                          M.get_name (| globals, "d2" |)
                        |)
                      |),
                      BinOp.mult (|
                        M.get_name (| globals, "q_0" |),
                        M.get_subscript (|
                          M.get_name (| globals, "f2" |),
                          M.get_name (| globals, "i" |)
                        |)
                      |)
                    |),
                    M.get_name (| globals, "p" |)
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
              M.get_name (| globals, "i" |),
              M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, "self" |), "MODULUS" |)
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
                        M.get_name (| globals, "x1" |),
                        M.get_name (| globals, "i" |)
                      |),
                      Constant.int 0
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let d1 :=
                      M.get_name (| globals, "i" |) in
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
                      M.get_name (| globals, "d1" |),
                      Constant.int 0
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let ans :=
                      M.get_name (| globals, "f1" |) in
                    let q :=
                      M.call (|
                        M.get_name (| globals, "pow" |),
                        make_list [
                          M.get_subscript (|
                            M.get_name (| globals, "x1" |),
                            Constant.int 0
                          |);
                          UnOp.sub (| Constant.int 1 |);
                          M.get_field (| M.get_name (| globals, "self" |), "PRIME" |)
                        ],
                        make_dict []
                      |) in
                    let _ :=
                      M.for_ (|
                        M.get_name (| globals, "i" |),
                        M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "ans" |)
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
    M.get_name (| globals, "ans" |),
    M.get_name (| globals, "i" |)
  |),
                            M.get_name (| globals, "q" |)
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
                          M.get_name (| globals, "d2" |),
                          Constant.int 0
                        |),
                      (* then *)
                      ltac:(M.monadic (
                        let ans :=
                          M.get_name (| globals, "f2" |) in
                        let q :=
                          M.call (|
                            M.get_name (| globals, "pow" |),
                            make_list [
                              M.get_subscript (|
                                M.get_name (| globals, "x2" |),
                                Constant.int 0
                              |);
                              UnOp.sub (| Constant.int 1 |);
                              M.get_field (| M.get_name (| globals, "self" |), "PRIME" |)
                            ],
                            make_dict []
                          |) in
                        let _ :=
                          M.for_ (|
                            M.get_name (| globals, "i" |),
                            M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "ans" |)
          ],
          make_dict []
        |)
      ],
      make_dict []
    |),
                            ltac:(M.monadic (
                              let ans := BinOp.mult
                                M.get_name (| globals, "q" |)
                                M.get_name (| globals, "q" |) in
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
                      M.get_name (| globals, "d1" |),
                      M.get_name (| globals, "d2" |)
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let q :=
                      BinOp.mult (|
                        M.get_subscript (|
                          M.get_name (| globals, "x2" |),
                          M.get_name (| globals, "d2" |)
                        |),
                        M.call (|
                          M.get_name (| globals, "pow" |),
                          make_list [
                            M.get_subscript (|
                              M.get_name (| globals, "x1" |),
                              M.get_name (| globals, "d1" |)
                            |);
                            UnOp.sub (| Constant.int 1 |);
                            M.get_field (| M.get_name (| globals, "self" |), "PRIME" |)
                          ],
                          make_dict []
                        |)
                      |) in
                    let _ :=
                      M.for_ (|
                        M.get_name (| globals, "i" |),
                        M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, "self" |), "MODULUS" |)
            ],
            make_dict []
          |),
          BinOp.sub (|
            M.get_name (| globals, "d2" |),
            M.get_name (| globals, "d1" |)
          |)
        |)
      ],
      make_dict []
    |),
                        ltac:(M.monadic (
                          let _ := M.assign (|
                            M.get_subscript (|
                              M.get_name (| globals, "x2" |),
                              BinOp.add (|
                                M.get_name (| globals, "i" |),
                                BinOp.sub (|
                                  M.get_name (| globals, "d2" |),
                                  M.get_name (| globals, "d1" |)
                                |)
                              |)
                            |),
                            BinOp.mod_ (|
                              BinOp.sub (|
                                M.get_subscript (|
                                  M.get_name (| globals, "x2" |),
                                  BinOp.add (|
                                    M.get_name (| globals, "i" |),
                                    BinOp.sub (|
                                      M.get_name (| globals, "d2" |),
                                      M.get_name (| globals, "d1" |)
                                    |)
                                  |)
                                |),
                                BinOp.mult (|
                                  M.get_name (| globals, "q" |),
                                  M.get_subscript (|
                                    M.get_name (| globals, "x1" |),
                                    M.get_name (| globals, "i" |)
                                  |)
                                |)
                              |),
                              M.get_name (| globals, "p" |)
                            |)
                          |) in
                          let _ := M.assign (|
                            M.get_subscript (|
                              M.get_name (| globals, "f2" |),
                              BinOp.add (|
                                M.get_name (| globals, "i" |),
                                BinOp.sub (|
                                  M.get_name (| globals, "d2" |),
                                  M.get_name (| globals, "d1" |)
                                |)
                              |)
                            |),
                            BinOp.mod_ (|
                              BinOp.sub (|
                                M.get_subscript (|
                                  M.get_name (| globals, "f2" |),
                                  BinOp.add (|
                                    M.get_name (| globals, "i" |),
                                    BinOp.sub (|
                                      M.get_name (| globals, "d2" |),
                                      M.get_name (| globals, "d1" |)
                                    |)
                                  |)
                                |),
                                BinOp.mult (|
                                  M.get_name (| globals, "q" |),
                                  M.get_subscript (|
                                    M.get_name (| globals, "f1" |),
                                    M.get_name (| globals, "i" |)
                                  |)
                                |)
                              |),
                              M.get_name (| globals, "p" |)
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
        M.get_name (| globals, "x2" |),
        M.get_name (| globals, "d2" |)
      |),
      Constant.int 0
    |),
                        ltac:(M.monadic (
                          let d2 := BinOp.sub
                            Constant.int 1
                            Constant.int 1 in
                          M.pure Constant.None_
                        )),
                        ltac:(M.monadic (
                          M.pure Constant.None_
                        ))
                    |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    let q :=
                      BinOp.mult (|
                        M.get_subscript (|
                          M.get_name (| globals, "x1" |),
                          M.get_name (| globals, "d1" |)
                        |),
                        M.call (|
                          M.get_name (| globals, "pow" |),
                          make_list [
                            M.get_subscript (|
                              M.get_name (| globals, "x2" |),
                              M.get_name (| globals, "d2" |)
                            |);
                            UnOp.sub (| Constant.int 1 |);
                            M.get_field (| M.get_name (| globals, "self" |), "PRIME" |)
                          ],
                          make_dict []
                        |)
                      |) in
                    let _ :=
                      M.for_ (|
                        M.get_name (| globals, "i" |),
                        M.call (|
      M.get_name (| globals, "range" |),
      make_list [
        BinOp.sub (|
          M.call (|
            M.get_name (| globals, "len" |),
            make_list [
              M.get_field (| M.get_name (| globals, "self" |), "MODULUS" |)
            ],
            make_dict []
          |),
          BinOp.sub (|
            M.get_name (| globals, "d1" |),
            M.get_name (| globals, "d2" |)
          |)
        |)
      ],
      make_dict []
    |),
                        ltac:(M.monadic (
                          let _ := M.assign (|
                            M.get_subscript (|
                              M.get_name (| globals, "x1" |),
                              BinOp.add (|
                                M.get_name (| globals, "i" |),
                                BinOp.sub (|
                                  M.get_name (| globals, "d1" |),
                                  M.get_name (| globals, "d2" |)
                                |)
                              |)
                            |),
                            BinOp.mod_ (|
                              BinOp.sub (|
                                M.get_subscript (|
                                  M.get_name (| globals, "x1" |),
                                  BinOp.add (|
                                    M.get_name (| globals, "i" |),
                                    BinOp.sub (|
                                      M.get_name (| globals, "d1" |),
                                      M.get_name (| globals, "d2" |)
                                    |)
                                  |)
                                |),
                                BinOp.mult (|
                                  M.get_name (| globals, "q" |),
                                  M.get_subscript (|
                                    M.get_name (| globals, "x2" |),
                                    M.get_name (| globals, "i" |)
                                  |)
                                |)
                              |),
                              M.get_name (| globals, "p" |)
                            |)
                          |) in
                          let _ := M.assign (|
                            M.get_subscript (|
                              M.get_name (| globals, "f1" |),
                              BinOp.add (|
                                M.get_name (| globals, "i" |),
                                BinOp.sub (|
                                  M.get_name (| globals, "d1" |),
                                  M.get_name (| globals, "d2" |)
                                |)
                              |)
                            |),
                            BinOp.mod_ (|
                              BinOp.sub (|
                                M.get_subscript (|
                                  M.get_name (| globals, "f1" |),
                                  BinOp.add (|
                                    M.get_name (| globals, "i" |),
                                    BinOp.sub (|
                                      M.get_name (| globals, "d1" |),
                                      M.get_name (| globals, "d2" |)
                                    |)
                                  |)
                                |),
                                BinOp.mult (|
                                  M.get_name (| globals, "q" |),
                                  M.get_subscript (|
                                    M.get_name (| globals, "f2" |),
                                    M.get_name (| globals, "i" |)
                                  |)
                                |)
                              |),
                              M.get_name (| globals, "p" |)
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
        M.get_name (| globals, "x1" |),
        M.get_name (| globals, "d1" |)
      |),
      Constant.int 0
    |),
                        ltac:(M.monadic (
                          let d1 := BinOp.sub
                            Constant.int 1
                            Constant.int 1 in
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
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
                  ],
                  make_dict []
                |);
                M.get_name (| globals, "ans" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "exponent" ] |) in
          let degree :=
            M.call (|
              M.get_name (| globals, "len" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "MODULUS" |)
              ],
              make_dict []
            |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, "exponent" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let self :=
                M.call (|
                  M.get_field (| M.get_name (| globals, "self" |), "multiplicative_inverse" |),
                  make_list [],
                  make_dict []
                |) in
              let exponent :=
                UnOp.sub (| M.get_name (| globals, "exponent" |) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let res :=
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__new__" |),
              make_list [
                M.call (|
                  M.get_name (| globals, "type" |),
                  make_list [
                    M.get_name (| globals, "self" |)
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
                      M.get_name (| globals, "degree" |),
                      Constant.int 1
                    |)
                  |)
                |)
              ],
              make_dict []
            |) in
          let s :=
            M.get_name (| globals, "self" |) in
          let _ :=
            M.while (|
              Compare.not_eq (|
      M.get_name (| globals, "exponent" |),
      Constant.int 0
    |),
              ltac:(M.monadic (
                let _ :=
                  (* if *)
                  M.if_then_else (|
                    Compare.eq (|
                      BinOp.mod_ (|
                        M.get_name (| globals, "exponent" |),
                        Constant.int 2
                      |),
                      Constant.int 1
                    |),
                  (* then *)
                  ltac:(M.monadic (
                    let res := BinOp.mult
                      M.get_name (| globals, "s" |)
                      M.get_name (| globals, "s" |) in
                    M.pure Constant.None_
                  (* else *)
                  )), ltac:(M.monadic (
                    M.pure Constant.None_
                  )) |) in
                let s := BinOp.mult
                  M.get_name (| globals, "s" |)
                  M.get_name (| globals, "s" |) in
                let exponent := BinOp.floor_div
                  Constant.int 2
                  Constant.int 2 in
                M.pure Constant.None_
              )),
              ltac:(M.monadic (
                M.pure Constant.None_
              ))
          |) in
          let _ := M.return_ (|
            M.get_name (| globals, "res" |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__ipow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__pow__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "frobenius",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Returns `self ** p`. This function is known as the Frobenius
        endomorphism and has many special mathematical properties. In
        particular it is extremely cheap to compute compared to other
        exponentiations.
        " in
          let ans :=
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "from_int" |),
              make_list [
                Constant.int 0
              ],
              make_dict []
            |) in
(* At stmt: unsupported node type: AnnAssign *)
          let _ :=
            M.for_ (|
              make_tuple [ M.get_name (| globals, "i" |); M.get_name (| globals, "a" |) ],
              M.call (|
      M.get_name (| globals, "enumerate" |),
      make_list [
        M.get_name (| globals, "self" |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let ans := BinOp.add
                  M.call (|
    M.get_field (| M.call (|
      M.get_name (| globals, "cast" |),
      make_list [
        M.get_name (| globals, "U" |);
        M.get_subscript (|
          M.get_field (| M.get_name (| globals, "self" |), "FROBENIUS_COEFFICIENTS" |),
          M.get_name (| globals, "i" |)
        |)
      ],
      make_dict []
    |), "scalar_mul" |),
    make_list [
      M.get_name (| globals, "a" |)
    ],
    make_dict []
  |)
                  M.call (|
    M.get_field (| M.call (|
      M.get_name (| globals, "cast" |),
      make_list [
        M.get_name (| globals, "U" |);
        M.get_subscript (|
          M.get_field (| M.get_name (| globals, "self" |), "FROBENIUS_COEFFICIENTS" |),
          M.get_name (| globals, "i" |)
        |)
      ],
      make_dict []
    |), "scalar_mul" |),
    make_list [
      M.get_name (| globals, "a" |)
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
            M.get_name (| globals, "ans" |)
          |) in
          M.pure Constant.None_))
      )
    ].
