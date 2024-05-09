Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require dataclasses.
Axiom dataclasses_is_dataclass :
  IsGlobalAlias globals dataclasses.globals "is_dataclass".
Axiom dataclasses_replace :
  IsGlobalAlias globals dataclasses.globals "replace".

Require typing.
Axiom typing_Any :
  IsGlobalAlias globals typing.globals "Any".
Axiom typing_Callable :
  IsGlobalAlias globals typing.globals "Callable".
Axiom typing_ClassVar :
  IsGlobalAlias globals typing.globals "ClassVar".
Axiom typing_Optional :
  IsGlobalAlias globals typing.globals "Optional".
Axiom typing_Protocol :
  IsGlobalAlias globals typing.globals "Protocol".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".
Axiom typing_Type_ :
  IsGlobalAlias globals typing.globals "Type_".
Axiom typing_TypeVar :
  IsGlobalAlias globals typing.globals "TypeVar".
Axiom typing_runtime_checkable :
  IsGlobalAlias globals typing.globals "runtime_checkable".

Definition SlottedFreezable : Value.t :=
  builtins.make_klass
    [(globals, "Protocol")]
    [

    ]
    [

    ].

Definition U255_CEIL_VALUE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (| Constant.int 2, Constant.int 255 |))).

Definition expr_50 : Value.t :=
  Constant.str "
Smallest value that requires 256 bits to represent. Mostly used in signed
arithmetic operations, like [`sdiv`].

[`sdiv`]: ref:ethereum.frontier.vm.instructions.arithmetic.sdiv
".

Definition U256_CEIL_VALUE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (| Constant.int 2, Constant.int 256 |))).

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
        fun (args : list Value.t) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| [("cls", cls); ("buffer", buffer)] |) in
        let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its big endian representation.
        " in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |), [M.get_name (| globals, "buffer" |); Constant.str "big"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "from_le_bytes",
        fun (args : list Value.t) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| [("cls", cls); ("buffer", buffer)] |) in
        let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |), [M.get_name (| globals, "buffer" |); Constant.str "little"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ]
    [
      (
        "__init__",
        fun (args : list Value.t) =>
          match args with
          | [self; value] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("value", value)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "value" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "TypeError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "value" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__radd__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__add__" |), [M.get_name (| globals, "left" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__add__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__add__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__iadd__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__add__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__sub__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.lt (| M.get_name (| globals, "self" |), M.get_name (| globals, "right" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__sub__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rsub__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "self" |), M.get_name (| globals, "left" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rsub__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__isub__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__sub__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__mul__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__mul__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rmul__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__mul__" |), [M.get_name (| globals, "left" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__imul__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__mul__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__floordiv__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__floordiv__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rfloordiv__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rfloordiv__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__ifloordiv__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__floordiv__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__mod__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__mod__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rmod__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rmod__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__imod__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__mod__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__divmod__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let result := M.call (| M.get_field (| M.get_name (| globals, "int" |), "__divmod__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |) in
        let _ := M.return_ (| make_tuple [ M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 0 |)] |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 1 |)] |) ] |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rdivmod__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let result := M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rdivmod__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |) in
        let _ := M.return_ (| make_tuple [ M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 0 |)] |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 1 |)] |) ] |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__pow__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_; modulo] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_); ("modulo", modulo)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.is_not (| M.get_name (| globals, "modulo" |), Constant.None_ |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "modulo" |); M.get_name (| globals, "int" |)] |) |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.lt (| M.get_name (| globals, "modulo" |), Constant.int 0 |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
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
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__pow__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |); M.get_name (| globals, "modulo" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rpow__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_; modulo] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_); ("modulo", modulo)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.is_not (| M.get_name (| globals, "modulo" |), Constant.None_ |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "modulo" |); M.get_name (| globals, "int" |)] |) |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                Compare.lt (| M.get_name (| globals, "modulo" |), Constant.int 0 |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
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
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rpow__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |); M.get_name (| globals, "modulo" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__ipow__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_; modulo] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_); ("modulo", modulo)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__pow__" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "modulo" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__xor__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__xor__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rxor__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rxor__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__ixor__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__xor__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "to_be_bytes32",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its big endian
        representation with exactly 32 bytes.
        " in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "Bytes32" |), [M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [Constant.int 32; Constant.str "big"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "to_be_bytes",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its big endian
        representation, without padding.
        " in
        let bit_length := M.call (| M.get_field (| M.get_name (| globals, "self" |), "bit_length" |), [] |) in
        let byte_length := BinOp.floor_div (| BinOp.add (| M.get_name (| globals, "bit_length" |), Constant.int 7 |), Constant.int 8 |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [M.get_name (| globals, "byte_length" |); Constant.str "big"] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "to_le_bytes",
        fun (args : list Value.t) =>
          match args with
          | [self; number_bytes] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("number_bytes", number_bytes)] |) in
        let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its little endian
        representation, without padding.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.is (| M.get_name (| globals, "number_bytes" |), Constant.None_ |),
          (* then *)
          ltac:(M.monadic (
            let bit_length := M.call (| M.get_field (| M.get_name (| globals, "self" |), "bit_length" |), [] |) in
            let number_bytes := BinOp.floor_div (| BinOp.add (| M.get_name (| globals, "bit_length" |), Constant.int 7 |), Constant.int 8 |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [M.get_name (| globals, "number_bytes" |); Constant.str "little"] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ].

Definition T : Value.t := M.run ltac:(M.monadic (
  M.call (| M.get_name (| globals, "TypeVar" |), [Constant.str "T"] |))).

Definition FixedUint : Value.t :=
  builtins.make_klass
    [(globals, "int")]
    [

    ]
    [
      (
        "__init__",
        fun (args : list Value.t) =>
          match args with
          | [self; value] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("value", value)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "value" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "TypeError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "value" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "value" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__radd__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__add__" |), [M.get_name (| globals, "left" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__add__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let result := M.call (| M.get_field (| M.get_name (| globals, "int" |), "__add__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "result" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_name (| globals, "result" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "wrapping_add",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
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
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); BinOp.bit_and (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__add__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__iadd__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__add__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__sub__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            (* At expr: unsupported node type: BoolOp *),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__sub__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "wrapping_sub",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
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
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); BinOp.bit_and (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__sub__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rsub__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            (* At expr: unsupported node type: BoolOp *),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rsub__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__isub__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__sub__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__mul__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let result := M.call (| M.get_field (| M.get_name (| globals, "int" |), "__mul__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "result" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_name (| globals, "result" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "wrapping_mul",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
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
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); BinOp.bit_and (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__mul__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rmul__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__mul__" |), [M.get_name (| globals, "left" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__imul__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__mul__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__floordiv__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__floordiv__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rfloordiv__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "left" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rfloordiv__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__ifloordiv__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__floordiv__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__mod__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__mod__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rmod__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "left" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rmod__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__imod__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__mod__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__divmod__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let result := M.call (| M.get_field (| M.call (| M.get_name (| globals, "super" |), [M.get_name (| globals, "FixedUint" |); M.get_name (| globals, "self" |)] |), "__divmod__" |), [M.get_name (| globals, "right" |)] |) in
        let _ := M.return_ (| make_tuple [ M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 0 |)] |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 1 |)] |) ] |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rdivmod__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "left" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let result := M.call (| M.get_field (| M.call (| M.get_name (| globals, "super" |), [M.get_name (| globals, "FixedUint" |); M.get_name (| globals, "self" |)] |), "__rdivmod__" |), [M.get_name (| globals, "left" |)] |) in
        let _ := M.return_ (| make_tuple [ M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 0 |)] |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 1 |)] |) ] |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__pow__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_; modulo] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_); ("modulo", modulo)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.is_not (| M.get_name (| globals, "modulo" |), Constant.None_ |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "modulo" |); M.get_name (| globals, "int" |)] |) |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                BoolOp.or (|
Compare.lt (| M.get_name (| globals, "modulo" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "modulo" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
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
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let result := M.call (| M.get_field (| M.get_name (| globals, "int" |), "__pow__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |); M.get_name (| globals, "modulo" |)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            (* At expr: unsupported node type: BoolOp *),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.get_name (| globals, "result" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "wrapping_pow",
        fun (args : list Value.t) =>
          match args with
          | [self; right_; modulo] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_); ("modulo", modulo)] |) in
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
            Compare.is_not (| M.get_name (| globals, "modulo" |), Constant.None_ |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "modulo" |); M.get_name (| globals, "int" |)] |) |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                BoolOp.or (|
Compare.lt (| M.get_name (| globals, "modulo" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "modulo" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
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
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); BinOp.bit_and (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__pow__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |); M.get_name (| globals, "modulo" |)] |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rpow__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_; modulo] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_); ("modulo", modulo)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.is_not (| M.get_name (| globals, "modulo" |), Constant.None_ |),
          (* then *)
          ltac:(M.monadic (
            let _ :=
              (* if *)
              M.if_then_else (|
                UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "modulo" |); M.get_name (| globals, "int" |)] |) |),
              (* then *)
              ltac:(M.monadic (
                let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
                M.pure Constant.None_
              (* else *)
              )), ltac:(M.monadic (
                M.pure Constant.None_
              )) |) in
            let _ :=
              (* if *)
              M.if_then_else (|
                BoolOp.or (|
Compare.lt (| M.get_name (| globals, "modulo" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "modulo" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
              (* then *)
              ltac:(M.monadic (
                let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
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
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "left" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rpow__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |); M.get_name (| globals, "modulo" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__ipow__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_; modulo] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_); ("modulo", modulo)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__pow__" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "modulo" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__and__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__and__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__or__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__or__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__xor__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "right" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "right" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "right" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__xor__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "right" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rxor__",
        fun (args : list Value.t) =>
          match args with
          | [self; left_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("left_", left_)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "left" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            BoolOp.or (|
Compare.lt (| M.get_name (| globals, "left" |), Constant.int 0 |),
  ltac:(M.monadic (
Compare.gt (| M.get_name (| globals, "left" |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)
))
|),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "OverflowError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rxor__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "left" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__ixor__",
        fun (args : list Value.t) =>
          match args with
          | [self; right_] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("right_", right_)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "__xor__" |), [M.get_name (| globals, "right" |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__invert__",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); BinOp.bit_and (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__invert__" |), [M.get_name (| globals, "self" |)] |), M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |) |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "__rshift__",
        fun (args : list Value.t) =>
          match args with
          | [self; shift_by] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self); ("shift_by", shift_by)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            UnOp.not (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "shift_by" |); M.get_name (| globals, "int" |)] |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.get_name (| globals, "NotImplemented" |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "int" |), "__new__" |), [M.get_field (| M.get_name (| globals, "self" |), "__class__" |); M.call (| M.get_field (| M.get_name (| globals, "int" |), "__rshift__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "shift_by" |)] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "to_be_bytes",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Converts this unsigned integer into its big endian representation,
        omitting leading zero bytes.
        " in
        let bit_length := M.call (| M.get_field (| M.get_name (| globals, "self" |), "bit_length" |), [] |) in
        let byte_length := BinOp.floor_div (| BinOp.add (| M.get_name (| globals, "bit_length" |), Constant.int 7 |), Constant.int 8 |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [M.get_name (| globals, "byte_length" |); Constant.str "big"] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ].

Definition U256 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_be_bytes",
        fun (args : list Value.t) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| [("cls", cls); ("buffer", buffer)] |) in
        let _ := Constant.str "
        Converts a sequence of bytes into a fixed sized unsigned integer
        from its big endian representation.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt (| M.call (| M.get_name (| globals, "len" |), [M.get_name (| globals, "buffer" |)] |), Constant.int 32 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "ValueError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |), [M.get_name (| globals, "buffer" |); Constant.str "big"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "from_signed",
        fun (args : list Value.t) =>
          match args with
          | [cls; value] => ltac:(M.monadic (
            let _ := M.set_locals (| [("cls", cls); ("value", value)] |) in
        let _ := Constant.str "
        Creates an unsigned integer representing `value` using two's
        complement.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt_e (| M.get_name (| globals, "value" |), Constant.int 0 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.call (| M.get_name (| globals, "cls" |), [M.get_name (| globals, "value" |)] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "cls" |), [BinOp.bit_and (| M.get_name (| globals, "value" |), M.get_field (| M.get_name (| globals, "cls" |), "MAX_VALUE" |) |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ]
    [
      (
        "to_be_bytes32",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Converts this 256-bit unsigned integer into its big endian
        representation with exactly 32 bytes.
        " in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "Bytes32" |), [M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [Constant.int 32; Constant.str "big"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "to_signed",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Decodes a signed integer from its two's complement representation.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.lt (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "bit_length" |), [] |), Constant.int 256 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.return_ (| M.call (| M.get_name (| globals, "int" |), [M.get_name (| globals, "self" |)] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| BinOp.sub (| M.call (| M.get_name (| globals, "int" |), [M.get_name (| globals, "self" |)] |), M.get_name (| globals, "U256_CEIL_VALUE" |) |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition U32 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_le_bytes",
        fun (args : list Value.t) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| [("cls", cls); ("buffer", buffer)] |) in
        let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt (| M.call (| M.get_name (| globals, "len" |), [M.get_name (| globals, "buffer" |)] |), Constant.int 4 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "ValueError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |), [M.get_name (| globals, "buffer" |); Constant.str "little"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ]
    [
      (
        "to_le_bytes4",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, with exactly 4 bytes.
        " in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "Bytes4" |), [M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [Constant.int 4; Constant.str "little"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "to_le_bytes",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, in the fewest bytes possible.
        " in
        let bit_length := M.call (| M.get_field (| M.get_name (| globals, "self" |), "bit_length" |), [] |) in
        let byte_length := BinOp.floor_div (| BinOp.add (| M.get_name (| globals, "bit_length" |), Constant.int 7 |), Constant.int 8 |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [M.get_name (| globals, "byte_length" |); Constant.str "little"] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition U64 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_le_bytes",
        fun (args : list Value.t) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| [("cls", cls); ("buffer", buffer)] |) in
        let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt (| M.call (| M.get_name (| globals, "len" |), [M.get_name (| globals, "buffer" |)] |), Constant.int 8 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "ValueError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |), [M.get_name (| globals, "buffer" |); Constant.str "little"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "from_be_bytes",
        fun (args : list Value.t) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| [("cls", cls); ("buffer", buffer)] |) in
        let _ := Constant.str "
        Converts a sequence of bytes into an unsigned 64 bit integer from its
        big endian representation.
        " in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.gt (| M.call (| M.get_name (| globals, "len" |), [M.get_name (| globals, "buffer" |)] |), Constant.int 8 |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "ValueError" |), [] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |), [M.get_name (| globals, "buffer" |); Constant.str "big"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ]
    [
      (
        "to_le_bytes8",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, with exactly 8 bytes.
        " in
        let _ := M.return_ (| M.call (| M.get_name (| globals, "Bytes8" |), [M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [Constant.int 8; Constant.str "little"] |)] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "to_le_bytes",
        fun (args : list Value.t) =>
          match args with
          | [self] => ltac:(M.monadic (
            let _ := M.set_locals (| [("self", self)] |) in
        let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, in the fewest bytes possible.
        " in
        let bit_length := M.call (| M.get_field (| M.get_name (| globals, "self" |), "bit_length" |), [] |) in
        let byte_length := BinOp.floor_div (| BinOp.add (| M.get_name (| globals, "bit_length" |), Constant.int 7 |), Constant.int 8 |) in
        let _ := M.return_ (| M.call (| M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |), [M.get_name (| globals, "byte_length" |); Constant.str "little"] |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition B : Value.t := M.run ltac:(M.monadic (
  M.call (| M.get_name (| globals, "TypeVar" |), [Constant.str "B"] |))).

Definition FixedBytes : Value.t :=
  builtins.make_klass
    [(globals, "bytes")]
    [

    ]
    [
      (
        "__new__",
        fun (args : list Value.t) =>
          match args with
          | [cls] => ltac:(M.monadic (
            let _ := M.set_locals (| [("cls", cls)] |) in
        let _ := Constant.str "
        Create a new instance, ensuring the result has the correct length.
        " in
        let result := M.call (| M.get_field (| M.call (| M.get_name (| globals, "super" |), [M.get_name (| globals, "FixedBytes" |); M.get_name (| globals, "cls" |)] |), "__new__" |), [M.get_name (| globals, "cls" |); *M.get_name (| globals, "args" |)] |) in
        let _ :=
          (* if *)
          M.if_then_else (|
            Compare.not_eq (| M.call (| M.get_name (| globals, "len" |), [M.get_name (| globals, "result" |)] |), M.get_field (| M.get_name (| globals, "cls" |), "LENGTH" |) |),
          (* then *)
          ltac:(M.monadic (
            let _ := M.raise (| M.call (| M.get_name (| globals, "ValueError" |), [(* At expr: unsupported node type: JoinedStr *)] |) |) in
            M.pure Constant.None_
          (* else *)
          )), ltac:(M.monadic (
            M.pure Constant.None_
          )) |) in
        let _ := M.return_ (| M.get_name (| globals, "result" |) |) in
        M.pure Constant.None_))
          | _ => M.impossible
          end
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
  M.get_name (| globals, "bytes" |))).

Definition expr_925 : Value.t :=
  Constant.str "
Sequence of bytes (octets) of arbitrary length.
".

Definition _setattr_function (args : list Value.t) : M :=
  match args with
  | [self; attr; value] => ltac:(M.monadic (
  let _ :=
    (* if *)
    M.if_then_else (|
      M.call (| M.get_name (| globals, "getattr" |), [M.get_name (| globals, "self" |); Constant.str "_frozen"; Constant.None_] |),
    (* then *)
    ltac:(M.monadic (
      let _ := M.raise (| M.call (| M.get_name (| globals, "Exception" |), [Constant.str "Mutating frozen dataclasses is not allowed."] |) |) in
      M.pure Constant.None_
    (* else *)
    )), ltac:(M.monadic (
      let _ := M.call (| M.get_field (| M.get_name (| globals, "object" |), "__setattr__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "attr" |); M.get_name (| globals, "value" |)] |) in
      M.pure Constant.None_
    )) |) in))
  | _ => M.impossible
  end.

Definition _delattr_function (args : list Value.t) : M :=
  match args with
  | [self; attr] => ltac:(M.monadic (
  let _ :=
    (* if *)
    M.if_then_else (|
      M.get_field (| M.get_name (| globals, "self" |), "_frozen" |),
    (* then *)
    ltac:(M.monadic (
      let _ := M.raise (| M.call (| M.get_name (| globals, "Exception" |), [Constant.str "Mutating frozen dataclasses is not allowed."] |) |) in
      M.pure Constant.None_
    (* else *)
    )), ltac:(M.monadic (
      let _ := M.call (| M.get_field (| M.get_name (| globals, "object" |), "__delattr__" |), [M.get_name (| globals, "self" |); M.get_name (| globals, "attr" |)] |) in
      M.pure Constant.None_
    )) |) in))
  | _ => M.impossible
  end.

Definition _make_init_function (args : list Value.t) : M :=
  match args with
  | [f] => ltac:(M.monadic (
(* At stmt: unsupported node type: FunctionDef *)
  let _ := M.return_ (| M.get_name (| globals, "init_function" |) |) in))
  | _ => M.impossible
  end.

Definition slotted_freezable (args : list Value.t) : M :=
  match args with
  | [cls] => ltac:(M.monadic (
  let _ := Constant.str "
    Monkey patches a dataclass so it can be frozen by setting `_frozen` to
    `True` and uses `__slots__` for efficiency.

    Instances will be created frozen by default unless you pass `_frozen=False`
    to `__init__`.
    " in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, "cls" |), "__slots__" |),
    BinOp.add (| make_tuple [ Constant.str "_frozen" ], M.call (| M.get_name (| globals, "tuple" |), [M.get_field (| M.get_name (| globals, "cls" |), "__annotations__" |)] |) |)
  |) in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, "cls" |), "__init__" |),
    M.call (| M.get_name (| globals, "_make_init_function" |), [M.get_field (| M.get_name (| globals, "cls" |), "__init__" |)] |)
  |) in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, "cls" |), "__setattr__" |),
    M.get_name (| globals, "_setattr_function" |)
  |) in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, "cls" |), "__delattr__" |),
    M.get_name (| globals, "_delattr_function" |)
  |) in
  let _ := M.return_ (| M.call (| M.call (| M.get_name (| globals, "type" |), [M.get_name (| globals, "cls" |)] |), [M.get_field (| M.get_name (| globals, "cls" |), "__name__" |); M.get_field (| M.get_name (| globals, "cls" |), "__bases__" |); M.call (| M.get_name (| globals, "dict" |), [M.get_field (| M.get_name (| globals, "cls" |), "__dict__" |)] |)] |) |) in))
  | _ => M.impossible
  end.

Definition S : Value.t := M.run ltac:(M.monadic (
  M.call (| M.get_name (| globals, "TypeVar" |), [Constant.str "S"] |))).

Definition modify (args : list Value.t) : M :=
  match args with
  | [obj; f] => ltac:(M.monadic (
  let _ := Constant.str "
    Create a copy of `obj` (which must be [`@slotted_freezable`]), and modify
    it by applying `f`. The returned copy will be frozen.

    [`@slotted_freezable`]: ref:ethereum.base_types.slotted_freezable
    " in
  let _ := M.assert (| M.call (| M.get_name (| globals, "is_dataclass" |), [M.get_name (| globals, "obj" |)] |) |) in
  let _ := M.assert (| M.call (| M.get_name (| globals, "isinstance" |), [M.get_name (| globals, "obj" |); M.get_name (| globals, "SlottedFreezable" |)] |) |) in
  let new_obj := M.call (| M.get_name (| globals, "replace" |), [M.get_name (| globals, "obj" |)] |) in
  let _ := M.call (| M.get_name (| globals, "f" |), [M.get_name (| globals, "new_obj" |)] |) in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, "new_obj" |), "_frozen" |),
    Constant.bool true
  |) in
  let _ := M.return_ (| M.get_name (| globals, "new_obj" |) |) in))
  | _ => M.impossible
  end.
