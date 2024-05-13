Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.crypto.alt_bn128".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
The alt_bn128 curve
^^^^^^^^^^^^^^^^^^^
".

Axiom ethereum_crypto_imports_elliptic_curve :
  IsImported globals "ethereum.crypto" "elliptic_curve".
Axiom ethereum_crypto_imports_finite_field :
  IsImported globals "ethereum.crypto" "finite_field".

Definition ALT_BN128_PRIME : Value.t := M.run ltac:(M.monadic (
  Constant.int 21888242871839275222246405745257275088696311157297823662689037894645226208583
)).

Definition ALT_BN128_CURVE_ORDER : Value.t := M.run ltac:(M.monadic (
  Constant.int 21888242871839275222246405745257275088548364400416034343698204186575808495617
)).

Definition ATE_PAIRING_COUNT : Value.t := M.run ltac:(M.monadic (
  Constant.int 29793968203157093289
)).

Definition ATE_PAIRING_COUNT_BITS : Value.t := M.run ltac:(M.monadic (
  Constant.int 63
)).

Definition BNF : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

Definition BNP : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

Definition BNF2 : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition expr_45 : Value.t :=
  Constant.str "autoapi_noindex".

(* At top_level_stmt: unsupported node type: Assign *)

Definition expr_48 : Value.t :=
  Constant.str "autoapi_noindex".

(* At top_level_stmt: unsupported node type: Assign *)

Definition expr_51 : Value.t :=
  Constant.str "autoapi_noindex".

Definition BNP2 : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

Definition BNF12 : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [
      (
        "__mul__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Multiplication special cased for BNF12.
        " in
          let _ := M.assign_local (|
            "mul" ,
            BinOp.mult (|
              make_list [
                Constant.int 0
              ],
              Constant.int 23
            |)
          |) in
          let _ :=
            M.for_ (|
              M.get_name (| globals, locals_stack, "i" |),
              M.call (|
      M.get_name (| globals, locals_stack, "range" |),
      make_list [
        Constant.int 12
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
        Constant.int 12
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
        Constant.int 22;
        Constant.int 11;
        UnOp.sub (| Constant.int 1 |)
      ],
      make_dict []
    |),
              ltac:(M.monadic (
                let _ := M.assign_op (|
                  BinOp.sub,
                  M.get_subscript (|
    M.get_name (| globals, locals_stack, "mul" |),
    BinOp.sub (|
      M.get_name (| globals, locals_stack, "i" |),
      Constant.int 6
    |)
  |),
                  BinOp.mult (|
    M.get_subscript (|
      M.get_name (| globals, locals_stack, "mul" |),
      M.get_name (| globals, locals_stack, "i" |)
    |),
    UnOp.sub (| Constant.int 18 |)
  |)
                |) in
                let _ := M.assign_op (|
                  BinOp.sub,
                  M.get_subscript (|
    M.get_name (| globals, locals_stack, "mul" |),
    BinOp.sub (|
      M.get_name (| globals, locals_stack, "i" |),
      Constant.int 12
    |)
  |),
                  BinOp.mult (|
    M.get_subscript (|
      M.get_name (| globals, locals_stack, "mul" |),
      M.get_name (| globals, locals_stack, "i" |)
    |),
    Constant.int 82
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
              M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "__new__" |),
              make_list [
                M.get_name (| globals, locals_stack, "BNF12" |);
                M.slice (|
                  M.get_name (| globals, locals_stack, "mul" |),
                  Constant.None_,
                  Constant.int 12,
                  Constant.None_
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition expr_98 : Value.t :=
  Constant.str "autoapi_noindex".

(* At top_level_stmt: unsupported node type: Assign *)

Definition expr_101 : Value.t :=
  Constant.str "autoapi_noindex".

(* At top_level_stmt: unsupported node type: Assign *)

Definition expr_104 : Value.t :=
  Constant.str "autoapi_noindex".

Definition BNP12 : Value.t :=
  builtins.make_klass
    [(* At base: unsupported node type: Attribute *)]
    [

    ]
    [

    ].

Definition bnf2_to_bnf12 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "x" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Lift a field element in `BNF2` to `BNF12`.
    " in
    let _ := M.return_ (|
      BinOp.add (|
        M.call (|
          M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
          make_list [
            M.get_subscript (|
              M.get_name (| globals, locals_stack, "x" |),
              Constant.int 0
            |)
          ],
          make_dict []
        |),
        BinOp.mult (|
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
            make_list [
              M.get_subscript (|
                M.get_name (| globals, locals_stack, "x" |),
                Constant.int 1
              |)
            ],
            make_dict []
          |),
          BinOp.sub (|
            M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "i_plus_9" |),
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
              make_list [
                Constant.int 9
              ],
              make_dict []
            |)
          |)
        |)
      |)
    |) in
    M.pure Constant.None_)).

Axiom bnf2_to_bnf12_in_globals :
  IsInGlobals globals "bnf2_to_bnf12" (make_function bnf2_to_bnf12).

Definition bnp_to_bnp12 : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "p" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Lift a point from `BNP` to `BNP12`.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "BNP12" |),
        make_list [
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "int" |),
                make_list [
                  M.get_field (| M.get_name (| globals, locals_stack, "p" |), "x" |)
                ],
                make_dict []
              |)
            ],
            make_dict []
          |);
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
            make_list [
              M.call (|
                M.get_name (| globals, locals_stack, "int" |),
                make_list [
                  M.get_field (| M.get_name (| globals, locals_stack, "p" |), "y" |)
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
    M.pure Constant.None_)).

Axiom bnp_to_bnp12_in_globals :
  IsInGlobals globals "bnp_to_bnp12" (make_function bnp_to_bnp12).

Definition twist : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "p" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Apply to twist to change variables from the curve `BNP2` to `BNP12`.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "BNP12" |),
        make_list [
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, locals_stack, "bnf2_to_bnf12" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "p" |), "x" |)
              ],
              make_dict []
            |),
            BinOp.pow (|
              M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "w" |),
              Constant.int 2
            |)
          |);
          BinOp.mult (|
            M.call (|
              M.get_name (| globals, locals_stack, "bnf2_to_bnf12" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "p" |), "y" |)
              ],
              make_dict []
            |),
            BinOp.pow (|
              M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "w" |),
              Constant.int 3
            |)
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom twist_in_globals :
  IsInGlobals globals "twist" (make_function twist).

Definition linefunc : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "p1"; "p2"; "t" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Evaluate the function defining the line between points `p1` and `p2` at the
    point `t`. The mathematical significance of this function is that is has
    divisor `(p1) + (p2) + (p1 + p2) - 3(O)`.

    Note: Abstract mathematical presentations of Miller's algorithm often
    specify the divisor `(p1) + (p2) - (p1 + p2) - (O)`. This turns out not to
    matter.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        Compare.not_eq (|
          M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "x" |),
          M.get_field (| M.get_name (| globals, locals_stack, "p2" |), "x" |)
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.assign_local (|
          "lam" ,
          BinOp.div (|
            BinOp.sub (|
              M.get_field (| M.get_name (| globals, locals_stack, "p2" |), "y" |),
              M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "y" |)
            |),
            BinOp.sub (|
              M.get_field (| M.get_name (| globals, locals_stack, "p2" |), "x" |),
              M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "x" |)
            |)
          |)
        |) in
        let _ := M.return_ (|
          BinOp.sub (|
            BinOp.mult (|
              M.get_name (| globals, locals_stack, "lam" |),
              BinOp.sub (|
                M.get_field (| M.get_name (| globals, locals_stack, "t" |), "x" |),
                M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "x" |)
              |)
            |),
            BinOp.sub (|
              M.get_field (| M.get_name (| globals, locals_stack, "t" |), "y" |),
              M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "y" |)
            |)
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.eq (|
              M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "y" |),
              M.get_field (| M.get_name (| globals, locals_stack, "p2" |), "y" |)
            |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.assign_local (|
              "lam" ,
              BinOp.div (|
                BinOp.mult (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
                    make_list [
                      Constant.int 3
                    ],
                    make_dict []
                  |),
                  BinOp.pow (|
                    M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "x" |),
                    Constant.int 2
                  |)
                |),
                BinOp.mult (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
                    make_list [
                      Constant.int 2
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "y" |)
                |)
              |)
            |) in
            let _ := M.return_ (|
              BinOp.sub (|
                BinOp.mult (|
                  M.get_name (| globals, locals_stack, "lam" |),
                  BinOp.sub (|
                    M.get_field (| M.get_name (| globals, locals_stack, "t" |), "x" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "x" |)
                  |)
                |),
                BinOp.sub (|
                  M.get_field (| M.get_name (| globals, locals_stack, "t" |), "y" |),
                  M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "y" |)
                |)
              |)
            |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            let _ := M.return_ (|
              BinOp.sub (|
                M.get_field (| M.get_name (| globals, locals_stack, "t" |), "x" |),
                M.get_field (| M.get_name (| globals, locals_stack, "p1" |), "x" |)
              |)
            |) in
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Axiom linefunc_in_globals :
  IsInGlobals globals "linefunc" (make_function linefunc).

Definition miller_loop : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "q"; "p" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    The core of the pairing algorithm.
    " in
    let _ :=
      (* if *)
      M.if_then_else (|
        BoolOp.or (|
          Compare.eq (|
            M.get_name (| globals, locals_stack, "p" |),
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "BNP12" |), "point_at_infinity" |),
              make_list [],
              make_dict []
            |)
          |),
          ltac:(M.monadic (
            Compare.eq (|
              M.get_name (| globals, locals_stack, "q" |),
              M.call (|
                M.get_field (| M.get_name (| globals, locals_stack, "BNP12" |), "point_at_infinity" |),
                make_list [],
                make_dict []
              |)
            |)
          ))
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.return_ (|
          M.call (|
            M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
            make_list [
              Constant.int 1
            ],
            make_dict []
          |)
        |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        M.pure Constant.None_
      )) |) in
    let _ := M.assign_local (|
      "r" ,
      M.get_name (| globals, locals_stack, "q" |)
    |) in
    let _ := M.assign_local (|
      "f" ,
      M.call (|
        M.get_field (| M.get_name (| globals, locals_stack, "BNF12" |), "from_int" |),
        make_list [
          Constant.int 1
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
        M.get_name (| globals, locals_stack, "ATE_PAIRING_COUNT_BITS" |);
        UnOp.sub (| Constant.int 1 |);
        UnOp.sub (| Constant.int 1 |)
      ],
      make_dict []
    |),
        ltac:(M.monadic (
          let _ := M.assign_local (|
            "f" ,
            BinOp.mult (|
              BinOp.mult (|
                M.get_name (| globals, locals_stack, "f" |),
                M.get_name (| globals, locals_stack, "f" |)
              |),
              M.call (|
                M.get_name (| globals, locals_stack, "linefunc" |),
                make_list [
                  M.get_name (| globals, locals_stack, "r" |);
                  M.get_name (| globals, locals_stack, "r" |);
                  M.get_name (| globals, locals_stack, "p" |)
                ],
                make_dict []
              |)
            |)
          |) in
          let _ := M.assign_local (|
            "r" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "r" |), "double" |),
              make_list [],
              make_dict []
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              BinOp.bit_and (|
                BinOp.sub (|
                  M.get_name (| globals, locals_stack, "ATE_PAIRING_COUNT" |),
                  Constant.int 1
                |),
                BinOp.pow (|
                  Constant.int 2,
                  M.get_name (| globals, locals_stack, "i" |)
                |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.assign_local (|
                "f" ,
                BinOp.mult (|
                  M.get_name (| globals, locals_stack, "f" |),
                  M.call (|
                    M.get_name (| globals, locals_stack, "linefunc" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "r" |);
                      M.get_name (| globals, locals_stack, "q" |);
                      M.get_name (| globals, locals_stack, "p" |)
                    ],
                    make_dict []
                  |)
                |)
              |) in
              let _ := M.assign_local (|
                "r" ,
                BinOp.add (|
                  M.get_name (| globals, locals_stack, "r" |),
                  M.get_name (| globals, locals_stack, "q" |)
                |)
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
    let _ := M.assert (| Compare.eq (|
    M.get_name (| globals, locals_stack, "r" |),
    M.call (|
      M.get_field (| M.get_name (| globals, locals_stack, "q" |), "mul_by" |),
      make_list [
        BinOp.sub (|
          M.get_name (| globals, locals_stack, "ATE_PAIRING_COUNT" |),
          Constant.int 1
        |)
      ],
      make_dict []
    |)
  |) |) in
    let _ := M.assign_local (|
      "q1" ,
      M.call (|
        M.get_name (| globals, locals_stack, "BNP12" |),
        make_list [
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "q" |), "x" |), "frobenius" |),
            make_list [],
            make_dict []
          |);
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "q" |), "y" |), "frobenius" |),
            make_list [],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "nq2" ,
      M.call (|
        M.get_name (| globals, locals_stack, "BNP12" |),
        make_list [
          M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "q1" |), "x" |), "frobenius" |),
            make_list [],
            make_dict []
          |);
          UnOp.sub (| M.call (|
            M.get_field (| M.get_field (| M.get_name (| globals, locals_stack, "q1" |), "y" |), "frobenius" |),
            make_list [],
            make_dict []
          |) |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign_local (|
      "f" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "f" |),
        M.call (|
          M.get_name (| globals, locals_stack, "linefunc" |),
          make_list [
            M.get_name (| globals, locals_stack, "r" |);
            M.get_name (| globals, locals_stack, "q1" |);
            M.get_name (| globals, locals_stack, "p" |)
          ],
          make_dict []
        |)
      |)
    |) in
    let _ := M.assign_local (|
      "r" ,
      BinOp.add (|
        M.get_name (| globals, locals_stack, "r" |),
        M.get_name (| globals, locals_stack, "q1" |)
      |)
    |) in
    let _ := M.assign_local (|
      "f" ,
      BinOp.mult (|
        M.get_name (| globals, locals_stack, "f" |),
        M.call (|
          M.get_name (| globals, locals_stack, "linefunc" |),
          make_list [
            M.get_name (| globals, locals_stack, "r" |);
            M.get_name (| globals, locals_stack, "nq2" |);
            M.get_name (| globals, locals_stack, "p" |)
          ],
          make_dict []
        |)
      |)
    |) in
    let _ := M.return_ (|
      BinOp.pow (|
        M.get_name (| globals, locals_stack, "f" |),
        BinOp.floor_div (|
          BinOp.sub (|
            BinOp.pow (|
              M.get_name (| globals, locals_stack, "ALT_BN128_PRIME" |),
              Constant.int 12
            |),
            Constant.int 1
          |),
          M.get_name (| globals, locals_stack, "ALT_BN128_CURVE_ORDER" |)
        |)
      |)
    |) in
    M.pure Constant.None_)).

Axiom miller_loop_in_globals :
  IsInGlobals globals "miller_loop" (make_function miller_loop).

Definition pairing : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "q"; "p" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Compute the pairing of `q` and `p`.
    " in
    let _ := M.return_ (|
      M.call (|
        M.get_name (| globals, locals_stack, "miller_loop" |),
        make_list [
          M.call (|
            M.get_name (| globals, locals_stack, "twist" |),
            make_list [
              M.get_name (| globals, locals_stack, "q" |)
            ],
            make_dict []
          |);
          M.call (|
            M.get_name (| globals, locals_stack, "bnp_to_bnp12" |),
            make_list [
              M.get_name (| globals, locals_stack, "p" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Axiom pairing_in_globals :
  IsInGlobals globals "pairing" (make_function pairing).
