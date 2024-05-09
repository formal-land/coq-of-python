Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Elliptic Curves
^^^^^^^^^^^^^^^
".

Require typing.
Axiom typing_Generic :
  IsGlobalAlias globals typing.globals "Generic".
Axiom typing_Type_ :
  IsGlobalAlias globals typing.globals "Type_".
Axiom typing_TypeVar :
  IsGlobalAlias globals typing.globals "TypeVar".

(* At top_level_stmt: unsupported node type: Import *)

Require base_types.
Axiom base_types_U256 :
  IsGlobalAlias globals base_types.globals "U256".
Axiom base_types_Bytes :
  IsGlobalAlias globals base_types.globals "Bytes".

Require finite_field.
Axiom finite_field_Field :
  IsGlobalAlias globals finite_field.globals "Field".

Require hash.
Axiom hash_Hash32 :
  IsGlobalAlias globals hash.globals "Hash32".

Definition SECP256K1N : Value.t := M.run ltac:(M.monadic (
  Constant.int 115792089237316195423570985008687907852837564279074904382605163141518161494337
)).

Definition F : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
    make_list [
      Constant.str "F"
    ],
    make_dict []
  |)
)).

Definition T : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
    make_list [
      Constant.str "T"
    ],
    make_dict []
  |)
)).

Definition secp256k1_recover : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "r"; "s"; "v"; "msg_hash" ] |) in
    let _ := Constant.str "
    Recovers the public key from a given signature.

    Parameters
    ----------
    r :
        TODO
    s :
        TODO
    v :
        TODO
    msg_hash :
        Hash of the message being recovered.

    Returns
    -------
    public_key : `ethereum.base_types.Bytes`
        Recovered public key.
    " in
    let r_bytes :=
      M.call (|
        M.get_field (| M.get_name (| globals, "r" |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |) in
    let s_bytes :=
      M.call (|
        M.get_field (| M.get_name (| globals, "s" |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |) in
    let signature :=
      M.call (|
        M.get_name (| globals, "bytearray" |),
        make_list [
          BinOp.mult (|
            make_list [
              Constant.int 0
            ],
            Constant.int 65
          |)
        ],
        make_dict []
      |) in
    let _ := M.assign (|
      M.get_subscript (| M.get_name (| globals, "signature" |), BinOp.sub (|
        Constant.int 32,
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "r_bytes" |)
          ],
          make_dict []
        |)
      |) |),
      M.get_name (| globals, "r_bytes" |)
    |) in
    let _ := M.assign (|
      M.get_subscript (| M.get_name (| globals, "signature" |), BinOp.sub (|
        Constant.int 64,
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "s_bytes" |)
          ],
          make_dict []
        |)
      |) |),
      M.get_name (| globals, "s_bytes" |)
    |) in
    let _ := M.assign (|
      M.get_subscript (| M.get_name (| globals, "signature" |), Constant.int 64 |),
      M.get_name (| globals, "v" |)
    |) in
    let public_key :=
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, "coincurve" |), "PublicKey" |), "from_signature_and_message" |),
        make_list [
          M.call (|
            M.get_name (| globals, "bytes" |),
            make_list [
              M.get_name (| globals, "signature" |)
            ],
            make_dict []
          |);
          M.get_name (| globals, "msg_hash" |)
        ],
        make_dict []
      |) in
    let public_key :=
      M.get_subscript (| M.call (|
        M.get_field (| M.get_name (| globals, "public_key" |), "format" |),
        make_list [],
        make_dict []
      |), Constant.int 1 |) in
    let _ := M.return_ (|
      M.get_name (| globals, "public_key" |)
    M.pure Constant.None_)).

Definition EllipticCurve : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Subscript *)]
    [
      (
        "point_at_infinity",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls" ] |) in
          let _ := Constant.str "
        Return the point at infinity. This is the identity element of the group
        operation.

        The point at infinity doesn't actually have coordinates so we use
        `(0, 0)` (which isn't on the curve) to represent it.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "cls" |), "__new__" |),
              make_list [
                M.get_name (| globals, "cls" |);
                M.call (|
                  M.get_field (| M.get_field (| M.get_name (| globals, "cls" |), "FIELD" |), "zero" |),
                  make_list [],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_field (| M.get_name (| globals, "cls" |), "FIELD" |), "zero" |),
                  make_list [],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      )
    ]
    [
      (
        "__new__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "x"; "y" ] |) in
          let _ := Constant.str "
        Make new point on the curve. The point is not checked to see if it is
        on the curve.
        " in
          let res :=
            M.call (|
              M.get_field (| M.get_name (| globals, "object" |), "__new__" |),
              make_list [
                M.get_name (| globals, "cls" |)
              ],
              make_dict []
            |) in
          let _ := M.assign (|
            M.get_field (| M.get_name (| globals, "res" |), "x" |),
            M.get_name (| globals, "x" |)
          |) in
          let _ := M.assign (|
            M.get_field (| M.get_name (| globals, "res" |), "y" |),
            M.get_name (| globals, "y" |)
          |) in
          let _ := M.return_ (|
            M.get_name (| globals, "res" |)
          M.pure Constant.None_))
      );
      (
        "__init__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "x"; "y" ] |) in
          let _ := Constant.str "
        Checks if the point is on the curve. To skip this check call
        `__new__()` directly.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_))
      );
      (
        "__eq__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "other" ] |) in
          let _ := Constant.str "
        Test two points for equality.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            BoolOp.and (|
              Compare.eq (|
                M.get_field (| M.get_name (| globals, "self" |), "x" |),
                M.get_field (| M.get_name (| globals, "other" |), "x" |)
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_field (| M.get_name (| globals, "self" |), "y" |),
                  M.get_field (| M.get_name (| globals, "other" |), "y" |)
                |)
              ))
            |)
          M.pure Constant.None_))
      );
      (
        "__str__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Stringify a point as its coordinates.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "str" |),
              make_list [
                make_tuple [ M.get_field (| M.get_name (| globals, "self" |), "x" |); M.get_field (| M.get_name (| globals, "self" |), "y" |) ]
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "double",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Add a point to itself.
        " in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, "x" |); M.get_name (| globals, "y" |); M.get_name (| globals, "F" |) ],
            make_tuple [ M.get_field (| M.get_name (| globals, "self" |), "x" |); M.get_field (| M.get_name (| globals, "self" |), "y" |); M.get_field (| M.get_name (| globals, "self" |), "FIELD" |) ]
          |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let lam :=
            BinOp.div (|
              BinOp.add (|
                BinOp.mult (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "F" |), "from_int" |),
                    make_list [
                      Constant.int 3
                    ],
                    make_dict []
                  |),
                  BinOp.pow (|
                    M.get_name (| globals, "x" |),
                    Constant.int 2
                  |)
                |),
                M.get_field (| M.get_name (| globals, "self" |), "A" |)
              |),
              BinOp.mult (|
                M.call (|
                  M.get_field (| M.get_name (| globals, "F" |), "from_int" |),
                  make_list [
                    Constant.int 2
                  ],
                  make_dict []
                |),
                M.get_name (| globals, "y" |)
              |)
            |) in
          let new_x :=
            BinOp.sub (|
              BinOp.sub (|
                BinOp.pow (|
                  M.get_name (| globals, "lam" |),
                  Constant.int 2
                |),
                M.get_name (| globals, "x" |)
              |),
              M.get_name (| globals, "x" |)
            |) in
          let new_y :=
            BinOp.sub (|
              BinOp.mult (|
                M.get_name (| globals, "lam" |),
                BinOp.sub (|
                  M.get_name (| globals, "x" |),
                  M.get_name (| globals, "new_x" |)
                |)
              |),
              M.get_name (| globals, "y" |)
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
                M.get_name (| globals, "new_x" |);
                M.get_name (| globals, "new_y" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "other" ] |) in
          let _ := Constant.str "
        Add two points together.
        " in
          let ZERO :=
            M.call (|
              M.get_field (| M.get_field (| M.get_name (| globals, "self" |), "FIELD" |), "zero" |),
              make_list [],
              make_dict []
            |) in
          let _ := M.assign (|
            make_tuple [ M.get_name (| globals, "self_x" |); M.get_name (| globals, "self_y" |); M.get_name (| globals, "other_x" |); M.get_name (| globals, "other_y" |) ],
            make_tuple [ M.get_field (| M.get_name (| globals, "self" |), "x" |); M.get_field (| M.get_name (| globals, "self" |), "y" |); M.get_field (| M.get_name (| globals, "other" |), "x" |); M.get_field (| M.get_name (| globals, "other" |), "y" |) ]
          |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let lam :=
            BinOp.div (|
              BinOp.sub (|
                M.get_name (| globals, "other_y" |),
                M.get_name (| globals, "self_y" |)
              |),
              BinOp.sub (|
                M.get_name (| globals, "other_x" |),
                M.get_name (| globals, "self_x" |)
              |)
            |) in
          let x :=
            BinOp.sub (|
              BinOp.sub (|
                BinOp.pow (|
                  M.get_name (| globals, "lam" |),
                  Constant.int 2
                |),
                M.get_name (| globals, "self_x" |)
              |),
              M.get_name (| globals, "other_x" |)
            |) in
          let y :=
            BinOp.sub (|
              BinOp.mult (|
                M.get_name (| globals, "lam" |),
                BinOp.sub (|
                  M.get_name (| globals, "self_x" |),
                  M.get_name (| globals, "x" |)
                |)
              |),
              M.get_name (| globals, "self_y" |)
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
                M.get_name (| globals, "x" |);
                M.get_name (| globals, "y" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "mul_by",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "n" ] |) in
          let _ := Constant.str "
        Multiply `self` by `n` using the double and add algorithm.
        " in
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
                M.call (|
                  M.get_field (| M.get_field (| M.get_name (| globals, "self" |), "FIELD" |), "zero" |),
                  make_list [],
                  make_dict []
                |);
                M.call (|
                  M.get_field (| M.get_field (| M.get_name (| globals, "self" |), "FIELD" |), "zero" |),
                  make_list [],
                  make_dict []
                |)
              ],
              make_dict []
            |) in
          let s :=
            M.get_name (| globals, "self" |) in
          While Compare.not_eq (|
    M.get_name (| globals, "n" |),
    Constant.int 0
  |) do
            let _ :=
                M.pure Constant.None_
              )) |) in
            let s :=
              BinOp.add (|
                M.get_name (| globals, "s" |),
                M.get_name (| globals, "s" |)
              |) in
            let n := BinOp.floor_div
              Constant.int 2
              Constant.int 2 in
          EndWhile.
          let _ := M.return_ (|
            M.get_name (| globals, "res" |)
          M.pure Constant.None_))
      )
    ].
