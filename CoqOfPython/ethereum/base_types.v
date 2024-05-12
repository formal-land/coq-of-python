Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.base_types".

Definition locals_stack : list Locals.t := [].

Definition expr_1 : Value.t :=
  Constant.str "
Integer and array types which are used by—but not unique to—Ethereum.

[`Uint`] represents non-negative integers of arbitrary size, while subclasses
of [`FixedUint`] (like [`U256`] or [`U32`]) represent non-negative integers of
particular sizes.

Similarly, [`Bytes`] represents arbitrarily long byte sequences, while
subclasses of [`FixedBytes`] (like [`Bytes0`] or [`Bytes64`]) represent
sequences containing an exact number of bytes.

[`Uint`]: ref:ethereum.base_types.Uint
[`FixedUint`]: ref:ethereum.base_types.FixedUint
[`U32`]: ref:ethereum.base_types.U32
[`U256`]: ref:ethereum.base_types.U256
[`Bytes`]: ref:ethereum.base_types.Bytes
[`FixedBytes`]: ref:ethereum.base_types.FixedBytes
[`Bytes0`]: ref:ethereum.base_types.Bytes0
[`Bytes64`]: ref:ethereum.base_types.Bytes64
".

Axiom dataclasses_imports_is_dataclass :
  IsImported globals "dataclasses" "is_dataclass".
Axiom dataclasses_imports_replace :
  IsImported globals "dataclasses" "replace".

Axiom typing_imports_Any :
  IsImported globals "typing" "Any".
Axiom typing_imports_Callable :
  IsImported globals "typing" "Callable".
Axiom typing_imports_ClassVar :
  IsImported globals "typing" "ClassVar".
Axiom typing_imports_Optional :
  IsImported globals "typing" "Optional".
Axiom typing_imports_Protocol :
  IsImported globals "typing" "Protocol".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".
Axiom typing_imports_Type :
  IsImported globals "typing" "Type".
Axiom typing_imports_TypeVar :
  IsImported globals "typing" "TypeVar".
Axiom typing_imports_runtime_checkable :
  IsImported globals "typing" "runtime_checkable".

Definition SlottedFreezable : Value.t :=
  builtins.make_klass
    [(globals, "Protocol")]
    [

    ]
    [

    ].

Definition U255_CEIL_VALUE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (|
    Constant.int 2,
    Constant.int 255
  |)
)).

Definition expr_50 : Value.t :=
  Constant.str "
Smallest value that requires 256 bits to represent. Mostly used in signed
arithmetic operations, like [`sdiv`].

[`sdiv`]: ref:ethereum.frontier.vm.instructions.arithmetic.sdiv
".

Definition U256_CEIL_VALUE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (|
    Constant.int 2,
    Constant.int 256
  |)
)).

Definition expr_58 : Value.t :=
  Constant.str "
Smallest value that requires 257 bits to represent. Used when converting a
[`U256`] in two's complement format to a regular `int` in [`U256.to_signed`].

[`U256`]: ref:ethereum.base_types.U256
[`U256.to_signed`]: ref:ethereum.base_types.U256.to_signed
".

Definition Uint : Value.t :=
  builtins.make_klass
    [(globals, "int")]
    [
      (
        "from_be_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "buffer" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its big endian representation.
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
        "from_le_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "buffer" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "cls" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "from_bytes" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "buffer" |);
                    Constant.str "little"
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ]
    [
      (
        "__init__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "value" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "value" |);
                  M.get_name (| globals, locals_stack, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "TypeError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "value" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "right" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.lt (|
                    M.get_name (| globals, locals_stack, "self" |),
                    M.get_name (| globals, locals_stack, "right" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "left" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "self" |),
                    M.get_name (| globals, locals_stack, "left" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
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
        "__isub__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__sub__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "right" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
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
        "__floordiv__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "right" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__floordiv__" |),
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
        "__rfloordiv__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "left" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rfloordiv__" |),
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
        "__ifloordiv__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__floordiv__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__mod__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "right" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__mod__" |),
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
        "__rmod__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "left" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rmod__" |),
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
        "__imod__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__mod__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__divmod__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "right" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_local (|
            "result" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__divmod__" |),
              make_list [
                M.get_name (| globals, locals_stack, "self" |);
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.return_ (|
            make_tuple [ M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "result" |),
                  Constant.int 0
                |)
              ],
              make_dict []
            |); M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "result" |),
                  Constant.int 1
                |)
              ],
              make_dict []
            |) ]
          |) in
          M.pure Constant.None_))
      );
      (
        "__rdivmod__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "left" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_local (|
            "result" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rdivmod__" |),
              make_list [
                M.get_name (| globals, locals_stack, "self" |);
                M.get_name (| globals, locals_stack, "left" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.return_ (|
            make_tuple [ M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "result" |),
                  Constant.int 0
                |)
              ],
              make_dict []
            |); M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "result" |),
                  Constant.int 1
                |)
              ],
              make_dict []
            |) ]
          |) in
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right"; "modulo" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.is_not (|
                M.get_name (| globals, locals_stack, "modulo" |),
                Constant.None_
              |),
            (* then *)
            ltac:(M.monadic (
              let _ :=
                (* if *)
                M.if_then_else (|
                  UnOp.not (| M.call (|
                    M.get_name (| globals, locals_stack, "isinstance" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "modulo" |);
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
              let _ :=
                (* if *)
                M.if_then_else (|
                  Compare.lt (|
                    M.get_name (| globals, locals_stack, "modulo" |),
                    Constant.int 0
                  |),
                (* then *)
                ltac:(M.monadic (
                  let _ := M.raise (| Some (M.call (|
                    M.get_name (| globals, locals_stack, "OverflowError" |),
                    make_list [],
                    make_dict []
                  |)) |) in
                  M.pure Constant.None_
                (* else *)
                )), ltac:(M.monadic (
                  M.pure Constant.None_
                )) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "right" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__pow__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |);
                    M.get_name (| globals, locals_stack, "right" |);
                    M.get_name (| globals, locals_stack, "modulo" |)
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
        "__rpow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left"; "modulo" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.is_not (|
                M.get_name (| globals, locals_stack, "modulo" |),
                Constant.None_
              |),
            (* then *)
            ltac:(M.monadic (
              let _ :=
                (* if *)
                M.if_then_else (|
                  UnOp.not (| M.call (|
                    M.get_name (| globals, locals_stack, "isinstance" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "modulo" |);
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
              let _ :=
                (* if *)
                M.if_then_else (|
                  Compare.lt (|
                    M.get_name (| globals, locals_stack, "modulo" |),
                    Constant.int 0
                  |),
                (* then *)
                ltac:(M.monadic (
                  let _ := M.raise (| Some (M.call (|
                    M.get_name (| globals, locals_stack, "OverflowError" |),
                    make_list [],
                    make_dict []
                  |)) |) in
                  M.pure Constant.None_
                (* else *)
                )), ltac:(M.monadic (
                  M.pure Constant.None_
                )) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "left" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rpow__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |);
                    M.get_name (| globals, locals_stack, "left" |);
                    M.get_name (| globals, locals_stack, "modulo" |)
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
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right"; "modulo" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__pow__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |);
                M.get_name (| globals, locals_stack, "modulo" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__xor__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "right" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__xor__" |),
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
        "__rxor__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.get_name (| globals, locals_stack, "left" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rxor__" |),
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
        "__ixor__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__xor__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
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
      );
      (
        "to_be_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its big endian
        representation, without padding.
        " in
          let _ := M.assign_local (|
            "bit_length" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "bit_length" |),
              make_list [],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "byte_length" ,
            BinOp.floor_div (|
              BinOp.add (|
                M.get_name (| globals, locals_stack, "bit_length" |),
                Constant.int 7
              |),
              Constant.int 8
            |)
          |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, locals_stack, "byte_length" |);
                Constant.str "big"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "to_le_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "number_bytes" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its little endian
        representation, without padding.
        " in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.is (|
                M.get_name (| globals, locals_stack, "number_bytes" |),
                Constant.None_
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.assign_local (|
                "bit_length" ,
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "bit_length" |),
                  make_list [],
                  make_dict []
                |)
              |) in
              let _ := M.assign_local (|
                "number_bytes" ,
                BinOp.floor_div (|
                  BinOp.add (|
                    M.get_name (| globals, locals_stack, "bit_length" |),
                    Constant.int 7
                  |),
                  Constant.int 8
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, locals_stack, "number_bytes" |);
                Constant.str "little"
              ],
              make_dict []
            |)
          |) in
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

Definition FixedUint : Value.t :=
  builtins.make_klass
    [(globals, "int")]
    [

    ]
    [
      (
        "__init__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "value" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "value" |);
                  M.get_name (| globals, locals_stack, "int" |)
                ],
                make_dict []
              |) |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "TypeError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "value" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "value" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
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
          let _ := M.assign_local (|
            "result" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__add__" |),
              make_list [
                M.get_name (| globals, locals_stack, "self" |);
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "result" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_name (| globals, locals_stack, "result" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "wrapping_add",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Return a new instance containing `self + right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        " in
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__add__" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |);
                      M.get_name (| globals, locals_stack, "right" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  BoolOp.or (|
                    Compare.gt (|
                      M.get_name (| globals, locals_stack, "right" |),
                      M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                    |),
                    ltac:(M.monadic (
                      Compare.lt (|
                        M.get_name (| globals, locals_stack, "self" |),
                        M.get_name (| globals, locals_stack, "right" |)
                      |)
                    ))
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
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
        "wrapping_sub",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Return a new instance containing `self - right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        " in
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__sub__" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |);
                      M.get_name (| globals, locals_stack, "right" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "left" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  BoolOp.or (|
                    Compare.gt (|
                      M.get_name (| globals, locals_stack, "left" |),
                      M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                    |),
                    ltac:(M.monadic (
                      Compare.gt (|
                        M.get_name (| globals, locals_stack, "self" |),
                        M.get_name (| globals, locals_stack, "left" |)
                      |)
                    ))
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
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
        "__isub__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__sub__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
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
          let _ := M.assign_local (|
            "result" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__mul__" |),
              make_list [
                M.get_name (| globals, locals_stack, "self" |);
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "result" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_name (| globals, locals_stack, "result" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "wrapping_mul",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Return a new instance containing `self * right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        " in
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__mul__" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |);
                      M.get_name (| globals, locals_stack, "right" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
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
        "__floordiv__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__floordiv__" |),
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
        "__rfloordiv__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "left" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "left" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rfloordiv__" |),
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
        "__ifloordiv__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__floordiv__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__mod__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__mod__" |),
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
        "__rmod__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "left" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "left" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rmod__" |),
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
        "__imod__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__mod__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__divmod__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_local (|
            "result" ,
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, locals_stack, "super" |),
                make_list [
                  M.get_name (| globals, locals_stack, "FixedUint" |);
                  M.get_name (| globals, locals_stack, "self" |)
                ],
                make_dict []
              |), "__divmod__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.return_ (|
            make_tuple [ M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "result" |),
                  Constant.int 0
                |)
              ],
              make_dict []
            |); M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "result" |),
                  Constant.int 1
                |)
              ],
              make_dict []
            |) ]
          |) in
          M.pure Constant.None_))
      );
      (
        "__rdivmod__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "left" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "left" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.assign_local (|
            "result" ,
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, locals_stack, "super" |),
                make_list [
                  M.get_name (| globals, locals_stack, "FixedUint" |);
                  M.get_name (| globals, locals_stack, "self" |)
                ],
                make_dict []
              |), "__rdivmod__" |),
              make_list [
                M.get_name (| globals, locals_stack, "left" |)
              ],
              make_dict []
            |)
          |) in
          let _ := M.return_ (|
            make_tuple [ M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "result" |),
                  Constant.int 0
                |)
              ],
              make_dict []
            |); M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_subscript (|
                  M.get_name (| globals, locals_stack, "result" |),
                  Constant.int 1
                |)
              ],
              make_dict []
            |) ]
          |) in
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right"; "modulo" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.is_not (|
                M.get_name (| globals, locals_stack, "modulo" |),
                Constant.None_
              |),
            (* then *)
            ltac:(M.monadic (
              let _ :=
                (* if *)
                M.if_then_else (|
                  UnOp.not (| M.call (|
                    M.get_name (| globals, locals_stack, "isinstance" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "modulo" |);
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
              let _ :=
                (* if *)
                M.if_then_else (|
                  BoolOp.or (|
                    Compare.lt (|
                      M.get_name (| globals, locals_stack, "modulo" |),
                      Constant.int 0
                    |),
                    ltac:(M.monadic (
                      Compare.gt (|
                        M.get_name (| globals, locals_stack, "modulo" |),
                        M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                      |)
                    ))
                  |),
                (* then *)
                ltac:(M.monadic (
                  let _ := M.raise (| Some (M.call (|
                    M.get_name (| globals, locals_stack, "OverflowError" |),
                    make_list [],
                    make_dict []
                  |)) |) in
                  M.pure Constant.None_
                (* else *)
                )), ltac:(M.monadic (
                  M.pure Constant.None_
                )) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
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
          let _ := M.assign_local (|
            "result" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__pow__" |),
              make_list [
                M.get_name (| globals, locals_stack, "self" |);
                M.get_name (| globals, locals_stack, "right" |);
                M.get_name (| globals, locals_stack, "modulo" |)
              ],
              make_dict []
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  BoolOp.or (|
                    Compare.gt (|
                      M.get_name (| globals, locals_stack, "right" |),
                      M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                    |),
                    ltac:(M.monadic (
                      Compare.gt (|
                        M.get_name (| globals, locals_stack, "result" |),
                        M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                      |)
                    ))
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.get_name (| globals, locals_stack, "result" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "wrapping_pow",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right"; "modulo" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Return a new instance containing `self ** right (mod modulo)`.

        If omitted, `modulo` defaults to `Uint(self.MAX_VALUE) + 1`.

        Passing a `right` or `modulo` value greater than [`MAX_VALUE`] or
        less than zero will raise a `ValueError`, even if the result would fit
        in this integer type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        " in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.is_not (|
                M.get_name (| globals, locals_stack, "modulo" |),
                Constant.None_
              |),
            (* then *)
            ltac:(M.monadic (
              let _ :=
                (* if *)
                M.if_then_else (|
                  UnOp.not (| M.call (|
                    M.get_name (| globals, locals_stack, "isinstance" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "modulo" |);
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
              let _ :=
                (* if *)
                M.if_then_else (|
                  BoolOp.or (|
                    Compare.lt (|
                      M.get_name (| globals, locals_stack, "modulo" |),
                      Constant.int 0
                    |),
                    ltac:(M.monadic (
                      Compare.gt (|
                        M.get_name (| globals, locals_stack, "modulo" |),
                        M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                      |)
                    ))
                  |),
                (* then *)
                ltac:(M.monadic (
                  let _ := M.raise (| Some (M.call (|
                    M.get_name (| globals, locals_stack, "OverflowError" |),
                    make_list [],
                    make_dict []
                  |)) |) in
                  M.pure Constant.None_
                (* else *)
                )), ltac:(M.monadic (
                  M.pure Constant.None_
                )) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__pow__" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |);
                      M.get_name (| globals, locals_stack, "right" |);
                      M.get_name (| globals, locals_stack, "modulo" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__rpow__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "left"; "modulo" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.is_not (|
                M.get_name (| globals, locals_stack, "modulo" |),
                Constant.None_
              |),
            (* then *)
            ltac:(M.monadic (
              let _ :=
                (* if *)
                M.if_then_else (|
                  UnOp.not (| M.call (|
                    M.get_name (| globals, locals_stack, "isinstance" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "modulo" |);
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
              let _ :=
                (* if *)
                M.if_then_else (|
                  BoolOp.or (|
                    Compare.lt (|
                      M.get_name (| globals, locals_stack, "modulo" |),
                      Constant.int 0
                    |),
                    ltac:(M.monadic (
                      Compare.gt (|
                        M.get_name (| globals, locals_stack, "modulo" |),
                        M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                      |)
                    ))
                  |),
                (* then *)
                ltac:(M.monadic (
                  let _ := M.raise (| Some (M.call (|
                    M.get_name (| globals, locals_stack, "OverflowError" |),
                    make_list [],
                    make_dict []
                  |)) |) in
                  M.pure Constant.None_
                (* else *)
                )), ltac:(M.monadic (
                  M.pure Constant.None_
                )) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "left" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "left" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rpow__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |);
                    M.get_name (| globals, locals_stack, "left" |);
                    M.get_name (| globals, locals_stack, "modulo" |)
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
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right"; "modulo" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__pow__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |);
                M.get_name (| globals, locals_stack, "modulo" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__and__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__and__" |),
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
        "__or__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__or__" |),
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
        "__xor__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "right" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "right" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__xor__" |),
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
        "__rxor__",
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
          let _ :=
            (* if *)
            M.if_then_else (|
              BoolOp.or (|
                Compare.lt (|
                  M.get_name (| globals, locals_stack, "left" |),
                  Constant.int 0
                |),
                ltac:(M.monadic (
                  Compare.gt (|
                    M.get_name (| globals, locals_stack, "left" |),
                    M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                  |)
                ))
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "OverflowError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rxor__" |),
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
        "__ixor__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "right" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__xor__" |),
              make_list [
                M.get_name (| globals, locals_stack, "right" |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__invert__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__invert__" |),
                    make_list [
                      M.get_name (| globals, locals_stack, "self" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      );
      (
        "__rshift__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "shift_by" ] in
          ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              UnOp.not (| M.call (|
                M.get_name (| globals, locals_stack, "isinstance" |),
                make_list [
                  M.get_name (| globals, locals_stack, "shift_by" |);
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
              M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, locals_stack, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "__rshift__" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |);
                    M.get_name (| globals, locals_stack, "shift_by" |)
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
        "to_be_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this unsigned integer into its big endian representation,
        omitting leading zero bytes.
        " in
          let _ := M.assign_local (|
            "bit_length" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "bit_length" |),
              make_list [],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "byte_length" ,
            BinOp.floor_div (|
              BinOp.add (|
                M.get_name (| globals, locals_stack, "bit_length" |),
                Constant.int 7
              |),
              Constant.int 8
            |)
          |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, locals_stack, "byte_length" |);
                Constant.str "big"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ].

Definition U256 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_be_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "buffer" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts a sequence of bytes into a fixed sized unsigned integer
        from its big endian representation.
        " in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt (|
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "buffer" |)
                  ],
                  make_dict []
                |),
                Constant.int 32
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "ValueError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
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
        "from_signed",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "value" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Creates an unsigned integer representing `value` using two's
        complement.
        " in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt_e (|
                M.get_name (| globals, locals_stack, "value" |),
                Constant.int 0
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.call (|
                  M.get_name (| globals, locals_stack, "cls" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "value" |)
                  ],
                  make_dict []
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "cls" |),
              make_list [
                BinOp.bit_and (|
                  M.get_name (| globals, locals_stack, "value" |),
                  M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ]
    [
      (
        "to_be_bytes32",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this 256-bit unsigned integer into its big endian
        representation with exactly 32 bytes.
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
      );
      (
        "to_signed",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Decodes a signed integer from its two's complement representation.
        " in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.lt (|
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "bit_length" |),
                  make_list [],
                  make_dict []
                |),
                Constant.int 256
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                M.call (|
                  M.get_name (| globals, locals_stack, "int" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "self" |)
                  ],
                  make_dict []
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            BinOp.sub (|
              M.call (|
                M.get_name (| globals, locals_stack, "int" |),
                make_list [
                  M.get_name (| globals, locals_stack, "self" |)
                ],
                make_dict []
              |),
              M.get_name (| globals, locals_stack, "U256_CEIL_VALUE" |)
            |)
          |) in
          M.pure Constant.None_))
      )
    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition U32 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_le_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "buffer" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt (|
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "buffer" |)
                  ],
                  make_dict []
                |),
                Constant.int 4
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "ValueError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "cls" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "from_bytes" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "buffer" |);
                    Constant.str "little"
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ]
    [
      (
        "to_le_bytes4",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, with exactly 4 bytes.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "Bytes4" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "to_bytes" |),
                  make_list [
                    Constant.int 4;
                    Constant.str "little"
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
        "to_le_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, in the fewest bytes possible.
        " in
          let _ := M.assign_local (|
            "bit_length" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "bit_length" |),
              make_list [],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "byte_length" ,
            BinOp.floor_div (|
              BinOp.add (|
                M.get_name (| globals, locals_stack, "bit_length" |),
                Constant.int 7
              |),
              Constant.int 8
            |)
          |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, locals_stack, "byte_length" |);
                Constant.str "little"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition U64 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_le_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "buffer" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt (|
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "buffer" |)
                  ],
                  make_dict []
                |),
                Constant.int 8
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "ValueError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "cls" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "int" |), "from_bytes" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "buffer" |);
                    Constant.str "little"
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
        "from_be_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls"; "buffer" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts a sequence of bytes into an unsigned 64 bit integer from its
        big endian representation.
        " in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.gt (|
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "buffer" |)
                  ],
                  make_dict []
                |),
                Constant.int 8
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "ValueError" |),
                make_list [],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
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
      )
    ]
    [
      (
        "to_le_bytes8",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, with exactly 8 bytes.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, locals_stack, "Bytes8" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, locals_stack, "self" |), "to_bytes" |),
                  make_list [
                    Constant.int 8;
                    Constant.str "little"
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
        "to_le_bytes",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "self" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, in the fewest bytes possible.
        " in
          let _ := M.assign_local (|
            "bit_length" ,
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "bit_length" |),
              make_list [],
              make_dict []
            |)
          |) in
          let _ := M.assign_local (|
            "byte_length" ,
            BinOp.floor_div (|
              BinOp.add (|
                M.get_name (| globals, locals_stack, "bit_length" |),
                Constant.int 7
              |),
              Constant.int 8
            |)
          |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, locals_stack, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, locals_stack, "byte_length" |);
                Constant.str "little"
              ],
              make_dict []
            |)
          |) in
          M.pure Constant.None_))
      )
    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition B : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "B"
    ],
    make_dict []
  |)
)).

Definition FixedBytes : Value.t :=
  builtins.make_klass
    [(globals, "bytes")]
    [

    ]
    [
      (
        "__new__",
        fun (args kwargs : Value.t) =>
          let- locals_stack := M.create_locals locals_stack args kwargs [ "cls" ] in
          ltac:(M.monadic (
          let _ := Constant.str "
        Create a new instance, ensuring the result has the correct length.
        " in
          let _ := M.assign_local (|
            "result" ,
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, locals_stack, "super" |),
                make_list [
                  M.get_name (| globals, locals_stack, "FixedBytes" |);
                  M.get_name (| globals, locals_stack, "cls" |)
                ],
                make_dict []
              |), "__new__" |),
              make_list_concat (| [
                make_list [
                  M.get_name (| globals, locals_stack, "cls" |)
                ];
                M.get_name (| globals, locals_stack, "args" |)
              ] |),
              make_dict []
            |)
          |) in
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.not_eq (|
                M.call (|
                  M.get_name (| globals, locals_stack, "len" |),
                  make_list [
                    M.get_name (| globals, locals_stack, "result" |)
                  ],
                  make_dict []
                |),
                M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "LENGTH" |)
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.raise (| Some (M.call (|
                M.get_name (| globals, locals_stack, "ValueError" |),
                make_list [
                  Constant.str "(* At expr: unsupported node type: JoinedStr *)"
                ],
                make_dict []
              |)) |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.get_name (| globals, locals_stack, "result" |)
          |) in
          M.pure Constant.None_))
      )
    ].

Definition Bytes0 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [

    ].

Definition Bytes4 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [

    ].

Definition Bytes8 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [

    ].

Definition Bytes20 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [

    ].

Definition Bytes32 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [

    ].

Definition Bytes48 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [

    ].

Definition Bytes64 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [

    ].

Definition Bytes256 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [

    ].

Definition Bytes : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, locals_stack, "bytes" |)
)).

Definition expr_925 : Value.t :=
  Constant.str "
Sequence of bytes (octets) of arbitrary length.
".

Definition _setattr_function : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "attr"; "value" ] in
    ltac:(M.monadic (
    let _ :=
      (* if *)
      M.if_then_else (|
        M.call (|
          M.get_name (| globals, locals_stack, "getattr" |),
          make_list [
            M.get_name (| globals, locals_stack, "self" |);
            Constant.str "_frozen";
            Constant.None_
          ],
          make_dict []
        |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.call (|
          M.get_name (| globals, locals_stack, "Exception" |),
          make_list [
            Constant.str "Mutating frozen dataclasses is not allowed."
          ],
          make_dict []
        |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "object" |), "__setattr__" |),
    make_list [
      M.get_name (| globals, locals_stack, "self" |);
      M.get_name (| globals, locals_stack, "attr" |);
      M.get_name (| globals, locals_stack, "value" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition _delattr_function : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "attr" ] in
    ltac:(M.monadic (
    let _ :=
      (* if *)
      M.if_then_else (|
        M.get_field (| M.get_name (| globals, locals_stack, "self" |), "_frozen" |),
      (* then *)
      ltac:(M.monadic (
        let _ := M.raise (| Some (M.call (|
          M.get_name (| globals, locals_stack, "Exception" |),
          make_list [
            Constant.str "Mutating frozen dataclasses is not allowed."
          ],
          make_dict []
        |)) |) in
        M.pure Constant.None_
      (* else *)
      )), ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.get_name (| globals, locals_stack, "object" |), "__delattr__" |),
    make_list [
      M.get_name (| globals, locals_stack, "self" |);
      M.get_name (| globals, locals_stack, "attr" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition _make_init_function : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "f" ] in
    ltac:(M.monadic (
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "init_function" |)
    |) in
    M.pure Constant.None_)).

Definition slotted_freezable : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "cls" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Monkey patches a dataclass so it can be frozen by setting `_frozen` to
    `True` and uses `__slots__` for efficiency.

    Instances will be created frozen by default unless you pass `_frozen=False`
    to `__init__`.
    " in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__slots__" |),
      BinOp.add (|
        make_tuple [ Constant.str "_frozen" ],
        M.call (|
          M.get_name (| globals, locals_stack, "tuple" |),
          make_list [
            M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__annotations__" |)
          ],
          make_dict []
        |)
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__init__" |),
      M.call (|
        M.get_name (| globals, locals_stack, "_make_init_function" |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__init__" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__setattr__" |),
      M.get_name (| globals, locals_stack, "_setattr_function" |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__delattr__" |),
      M.get_name (| globals, locals_stack, "_delattr_function" |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.call (|
          M.get_name (| globals, locals_stack, "type" |),
          make_list [
            M.get_name (| globals, locals_stack, "cls" |)
          ],
          make_dict []
        |),
        make_list [
          M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__name__" |);
          M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__bases__" |);
          M.call (|
            M.get_name (| globals, locals_stack, "dict" |),
            make_list [
              M.get_field (| M.get_name (| globals, locals_stack, "cls" |), "__dict__" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).

Definition S : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, locals_stack, "TypeVar" |),
    make_list [
      Constant.str "S"
    ],
    make_dict []
  |)
)).

Definition modify : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) =>
    let- locals_stack := M.create_locals locals_stack args kwargs [ "obj"; "f" ] in
    ltac:(M.monadic (
    let _ := Constant.str "
    Create a copy of `obj` (which must be [`@slotted_freezable`]), and modify
    it by applying `f`. The returned copy will be frozen.

    [`@slotted_freezable`]: ref:ethereum.base_types.slotted_freezable
    " in
    let _ := M.assert (| M.call (|
    M.get_name (| globals, locals_stack, "is_dataclass" |),
    make_list [
      M.get_name (| globals, locals_stack, "obj" |)
    ],
    make_dict []
  |) |) in
    let _ := M.assert (| M.call (|
    M.get_name (| globals, locals_stack, "isinstance" |),
    make_list [
      M.get_name (| globals, locals_stack, "obj" |);
      M.get_name (| globals, locals_stack, "SlottedFreezable" |)
    ],
    make_dict []
  |) |) in
    let _ := M.assign_local (|
      "new_obj" ,
      M.call (|
        M.get_name (| globals, locals_stack, "replace" |),
        make_list [
          M.get_name (| globals, locals_stack, "obj" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, locals_stack, "f" |),
    make_list [
      M.get_name (| globals, locals_stack, "new_obj" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, locals_stack, "new_obj" |), "_frozen" |),
      Constant.bool true
    |) in
    let _ := M.return_ (|
      M.get_name (| globals, locals_stack, "new_obj" |)
    |) in
    M.pure Constant.None_)).
