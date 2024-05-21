Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.crypto.elliptic_curve".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Elliptic Curves
^^^^^^^^^^^^^^^
".

Axiom typing_imports_Generic :
  IsImported globals "typing" "Generic".
Axiom typing_imports_Type :
  IsImported globals "typing" "Type".
Axiom typing_imports_TypeVar :
  IsImported globals "typing" "TypeVar".

(* At top_level_stmt: unsupported node type: Import *)

Axiom ethereum_base_types_imports_U256 :
  IsImported globals "ethereum.base_types" "U256".
Axiom ethereum_base_types_imports_Bytes :
  IsImported globals "ethereum.base_types" "Bytes".

Axiom ethereum_crypto_finite_field_imports_Field :
  IsImported globals "ethereum.crypto.finite_field" "Field".

Axiom ethereum_crypto_hash_imports_Hash32 :
  IsImported globals "ethereum.crypto.hash" "Hash32".

Definition SECP256K1N : Value.t := M.run ltac:(M.monadic (
  Constant.int 115792089237316195423570985008687907852837564279074904382605163141518161494337
)).

Definition F : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "F"
    ],
    make_dict []
  |)
)).

Definition T : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "T"
    ],
    make_dict []
  |)
)).

Definition secp256k1_recover : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "r"; "s"; "v"; "msg_hash" ] in
    ltac:(M.monadic (
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
    let _ := M.assign_local (|
      "r_bytes" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "r" |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "s_bytes" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "s" |), "to_be_bytes32" |),
        make_list [],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "signature" ,
      M.call (|
        M.get_name (| globals, locals_stack, "bytearray" |),
        make_list [
          BinOp.mult (|
            make_list [
              Constant.int 0
            ],
            Constant.int 65
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.slice (|
        M.get_name (| globals, locals_stack, "signature" |),
        BinOp.sub (|
          Constant.int 32,
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "r_bytes" |)
            ],
            make_dict []
          |)
        |),
        Constant.int 32,
        Constant.None_
      |),
      M.get_name (| globals, locals_stack, "r_bytes" |)
    |) in
    let _ := M.assign (|
      M.slice (|
        M.get_name (| globals, locals_stack, "signature" |),
        BinOp.sub (|
          Constant.int 64,
          M.call (|
            M.get_name (| globals, locals_stack, "len" |),
            make_list [
              M.get_name (| globals, locals_stack, "s_bytes" |)
            ],
            make_dict []
          |)
        |),
        Constant.int 64,
        Constant.None_
      |),
      M.get_name (| globals, locals_stack, "s_bytes" |)
    |) in
    let _ := M.assign (|
      M.get_subscript (|
        M.get_name (| globals, locals_stack, "signature" |),
        Constant.int 64
      |),
      M.get_name (| globals, locals_stack, "v" |)
    |) in
    let _ := M.assign_local (|
      "public_key" ,
      M.call (|
        M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "coincurve" |), "PublicKey" |), "from_signature_and_message" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "bytes" |),
            make_list [
              M.get_name (| globals, locals_stack, "signature" |)
            ],
            make_dict []
          |);
          M.get_name (| globals, locals_stack, "msg_hash" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "public_key" ,
      M.slice (|
        M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "public_key" |), "format" |),
          make_list [],
          make_dict []
        |),
        Constant.int 1,
        Constant.None_,
        Constant.None_
      |)
    |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "public_key" |)
    |) in
    M.pure Constant.None_)).

Axiom secp256k1_recover_in_globals :
  IsInGlobals globals "secp256k1_recover" (make_function secp256k1_recover).

Definition EllipticCurve : Value.t := make_klass {|
  Klass.bases := [
    (globals, "(* At base: unsupported node type: Subscript *)")
  ];
  Klass.class_methods := [
    (
      "point_at_infinity",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "cls" ] in
        ltac:(M.monadic (
        let _ := Constant.str "
        Return the point at infinity. This is the identity element of the group
        operation.

        The point at infinity doesn't actually have coordinates so we use
        `(0, 0)` (which isn't on the curve) to represent it.
        " in
        let _ := M.return_ (|
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__new__" |),
            make_list [
              M.get_name (| globals, locals_stack, "cls" |);
              M.call (|
                M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "FIELD" |), "zero" |),
                make_list [],
                make_dict []
              |);
              M.call (|
                M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "FIELD" |), "zero" |),
                make_list [],
                make_dict []
              |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_))
    )
  ];
  Klass.methods := [
    (
      "__new__",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "x"; "y" ] in
        ltac:(M.monadic (
        let _ := Constant.str "
        Make new point on the curve. The point is not checked to see if it is
        on the curve.
        " in
        let _ := M.assign_local (|
          "res" ,
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "object" |), "__new__" |),
            make_list [
              M.get_name (| globals, locals_stack, "cls" |)
            ],
            make_dict []
          |)
        |) in
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "res" |), "x" |),
          M.get_name (| globals, locals_stack, "x" |)
        |) in
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "res" |), "y" |),
          M.get_name (| globals, locals_stack, "y" |)
        |) in
        let _ := M.return_ (|
          M.get_name (| globals, locals_stack, "res" |)
        |) in
        M.pure Constant.None_))
    );
    (
      "__init__",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "x"; "y" ] in
        ltac:(M.monadic (
        let _ := Constant.str "
        Checks if the point is on the curve. To skip this check call
        `__new__()` directly.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              BoolOp.or (|
                Compare.not_eq (|
                  M.get_name (| globals, locals_stack, "x" |),
                  M.call (|
                    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "self" |), "FIELD" |), "zero" |),
                    make_list [],
                    make_dict []
                  |)
                |),
                ltac:(M.monadic (
                  Compare.not_eq (|
                    M.get_name (| globals, locals_stack, "y" |),
                    M.call (|
                      M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "self" |), "FIELD" |), "zero" |),
                      make_list [],
                      make_dict []
                    |)
                  |)
                ))
              |),
              ltac:(M.monadic (
                Compare.not_eq (|
                  BinOp.sub (|
                    BinOp.sub (|
                      BinOp.sub (|
                        BinOp.pow (|
                          M.get_name (| globals, locals_stack, "y" |),
                          Constant.int 2
                        |),
                        BinOp.pow (|
                          M.get_name (| globals, locals_stack, "x" |),
                          Constant.int 3
                        |)
                      |),
                      BinOp.mult (|
                        M.get_field (| M.get_name (| globals, locals_stack, "self" |), "A" |),
                        M.get_name (| globals, locals_stack, "x" |)
                      |)
                    |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "B" |)
                  |),
                  M.call (|
                    M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "self" |), "FIELD" |), "zero" |),
                    make_list [],
                    make_dict []
                  |)
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| Some (M.call (|
              M.get_name (| globals, locals_stack, "ValueError" |),
              make_list [
                Constant.str "Point not on curve"
              ],
              make_dict []
            |)) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_))
    );
    (
      "__eq__",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "other" ] in
        ltac:(M.monadic (
        let _ := Constant.str "
        Test two points for equality.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (|
              M.get_name (| globals, locals_stack, "isinstance" |),
              make_list [
                M.get_name (| globals, locals_stack, "other" |);
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
              Constant.bool false
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (|
          BoolOp.and (|
            Compare.eq (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "x" |),
              M.get_field (| M.get_name (| globals, locals_stack, "other" |), "x" |)
            |),
            ltac:(M.monadic (
              Compare.eq (|
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "y" |),
                M.get_field (| M.get_name (| globals, locals_stack, "other" |), "y" |)
              |)
            ))
          |)
        |) in
        M.pure Constant.None_))
    );
    (
      "__str__",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
        ltac:(M.monadic (
        let _ := Constant.str "
        Stringify a point as its coordinates.
        " in
        let _ := M.return_ (|
          M.call (|
            M.get_name (| globals, locals_stack, "str" |),
            make_list [
              make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "self" |), "x" |); M.get_field (| M.get_name (| globals, locals_stack, "self" |), "y" |) ]
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_))
    );
    (
      "double",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
        ltac:(M.monadic (
        let _ := Constant.str "
        Add a point to itself.
        " in
        let _ := M.assign (|
          make_tuple [ M.get_name (| globals, locals_stack, "x" |); M.get_name (| globals, locals_stack, "y" |); M.get_name (| globals, locals_stack, "F" |) ],
          make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "self" |), "x" |); M.get_field (| M.get_name (| globals, locals_stack, "self" |), "y" |); M.get_field (| M.get_name (| globals, locals_stack, "self" |), "FIELD" |) ]
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              Compare.eq (|
                M.get_name (| globals, locals_stack, "x" |),
                Constant.int 0
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_name (| globals, locals_stack, "y" |),
                  Constant.int 0
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.get_name (| globals, locals_stack, "self" |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.assign_local (|
          "lam" ,
          BinOp.div (|
            BinOp.add (|
              BinOp.mult (|
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "F" |), "from_int" |),
                  make_list [
                    Constant.int 3
                  ],
                  make_dict []
                |),
                BinOp.pow (|
                  M.get_name (| globals, locals_stack, "x" |),
                  Constant.int 2
                |)
              |),
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "A" |)
            |),
            BinOp.mult (|
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "F" |), "from_int" |),
                make_list [
                  Constant.int 2
                ],
                make_dict []
              |),
              M.get_name (| globals, locals_stack, "y" |)
            |)
          |)
        |) in
        let _ := M.assign_local (|
          "new_x" ,
          BinOp.sub (|
            BinOp.sub (|
              BinOp.pow (|
                M.get_name (| globals, locals_stack, "lam" |),
                Constant.int 2
              |),
              M.get_name (| globals, locals_stack, "x" |)
            |),
            M.get_name (| globals, locals_stack, "x" |)
          |)
        |) in
        let _ := M.assign_local (|
          "new_y" ,
          BinOp.sub (|
            BinOp.mult (|
              M.get_name (| globals, locals_stack, "lam" |),
              BinOp.sub (|
                M.get_name (| globals, locals_stack, "x" |),
                M.get_name (| globals, locals_stack, "new_x" |)
              |)
            |),
            M.get_name (| globals, locals_stack, "y" |)
          |)
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
              M.get_name (| globals, locals_stack, "new_x" |);
              M.get_name (| globals, locals_stack, "new_y" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_))
    );
    (
      "__add__",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "other" ] in
        ltac:(M.monadic (
        let _ := Constant.str "
        Add two points together.
        " in
        let _ := M.assign_local (|
          "ZERO" ,
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "self" |), "FIELD" |), "zero" |),
            make_list [],
            make_dict []
          |)
        |) in
        let _ := M.assign (|
          make_tuple [ M.get_name (| globals, locals_stack, "self_x" |); M.get_name (| globals, locals_stack, "self_y" |); M.get_name (| globals, locals_stack, "other_x" |); M.get_name (| globals, locals_stack, "other_y" |) ],
          make_tuple [ M.get_field (| M.get_name (| globals, locals_stack, "self" |), "x" |); M.get_field (| M.get_name (| globals, locals_stack, "self" |), "y" |); M.get_field (| M.get_name (| globals, locals_stack, "other" |), "x" |); M.get_field (| M.get_name (| globals, locals_stack, "other" |), "y" |) ]
        |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              Compare.eq (|
                M.get_name (| globals, locals_stack, "self_x" |),
                M.get_name (| globals, locals_stack, "ZERO" |)
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_name (| globals, locals_stack, "self_y" |),
                  M.get_name (| globals, locals_stack, "ZERO" |)
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.get_name (| globals, locals_stack, "other" |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.and (|
              Compare.eq (|
                M.get_name (| globals, locals_stack, "other_x" |),
                M.get_name (| globals, locals_stack, "ZERO" |)
              |),
              ltac:(M.monadic (
                Compare.eq (|
                  M.get_name (| globals, locals_stack, "other_y" |),
                  M.get_name (| globals, locals_stack, "ZERO" |)
                |)
              ))
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (|
              M.get_name (| globals, locals_stack, "self" |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_name (| globals, locals_stack, "self_x" |),
              M.get_name (| globals, locals_stack, "other_x" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.eq (|
                  M.get_name (| globals, locals_stack, "self_y" |),
                  M.get_name (| globals, locals_stack, "other_y" |)
                |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "double" |),
                    make_list [],
                    make_dict []
                  |)
                |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                let _ := M.return_ (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "point_at_infinity" |),
                    make_list [],
                    make_dict []
                  |)
                |) in
                M.pure Constant.None_
              )) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.assign_local (|
          "lam" ,
          BinOp.div (|
            BinOp.sub (|
              M.get_name (| globals, locals_stack, "other_y" |),
              M.get_name (| globals, locals_stack, "self_y" |)
            |),
            BinOp.sub (|
              M.get_name (| globals, locals_stack, "other_x" |),
              M.get_name (| globals, locals_stack, "self_x" |)
            |)
          |)
        |) in
        let _ := M.assign_local (|
          "x" ,
          BinOp.sub (|
            BinOp.sub (|
              BinOp.pow (|
                M.get_name (| globals, locals_stack, "lam" |),
                Constant.int 2
              |),
              M.get_name (| globals, locals_stack, "self_x" |)
            |),
            M.get_name (| globals, locals_stack, "other_x" |)
          |)
        |) in
        let _ := M.assign_local (|
          "y" ,
          BinOp.sub (|
            BinOp.mult (|
              M.get_name (| globals, locals_stack, "lam" |),
              BinOp.sub (|
                M.get_name (| globals, locals_stack, "self_x" |),
                M.get_name (| globals, locals_stack, "x" |)
              |)
            |),
            M.get_name (| globals, locals_stack, "self_y" |)
          |)
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
              M.get_name (| globals, locals_stack, "x" |);
              M.get_name (| globals, locals_stack, "y" |)
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_))
    );
    (
      "mul_by",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "n" ] in
        ltac:(M.monadic (
        let _ := Constant.str "
        Multiply `self` by `n` using the double and add algorithm.
        " in
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
              M.call (|
                M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "self" |), "FIELD" |), "zero" |),
                make_list [],
                make_dict []
              |);
              M.call (|
                M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "self" |), "FIELD" |), "zero" |),
                make_list [],
                make_dict []
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
      M.get_name (| globals, locals_stack, "n" |),
      Constant.int 0
    |),
            ltac:(M.monadic (
              let _ :=
                (* if *)
                M.if_then_else (|
                  Compare.eq (|
                    BinOp.mod_ (|
                      M.get_name (| globals, locals_stack, "n" |),
                      Constant.int 2
                    |),
                    Constant.int 1
                  |),
                (* then *)
                ltac:(M.monadic (
                  let _ := M.assign_local (|
                    "res" ,
                    BinOp.add (|
                      M.get_name (| globals, locals_stack, "res" |),
                      M.get_name (| globals, locals_stack, "s" |)
                    |)
                  |) in
                  M.pure Constant.None_
                (* else *)
                )), ltac:(M.monadic (
                  M.pure Constant.None_
                )) |) in
              let _ := M.assign_local (|
                "s" ,
                BinOp.add (|
                  M.get_name (| globals, locals_stack, "s" |),
                  M.get_name (| globals, locals_stack, "s" |)
                |)
              |) in
              let _ := M.assign_op_local (|
                BinOp.floor_div,
                "n",
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
    )
  ];
|}.
