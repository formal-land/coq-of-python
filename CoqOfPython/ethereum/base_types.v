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
    [].

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
        fun (args : list Value.t) (locals : nat) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| locals, [("cls", cls); ("buffer", buffer)] |) in
            let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its big endian representation.
        " in
            let _ := M.return_ (| M.call (| M.get_name (| globals, locals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, locals, "int" |), "from_bytes" |), [M.get_name (| globals, locals, "buffer" |); Constant.str "big"] |)] |) |) in
            M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "from_le_bytes",
        fun (args : list Value.t) (locals : nat) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| locals, [("cls", cls); ("buffer", buffer)] |) in
            let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
            let _ := M.return_ (| M.call (| M.get_name (| globals, locals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, locals, "int" |), "from_bytes" |), [M.get_name (| globals, locals, "buffer" |); Constant.str "little"] |)] |) |) in
            M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ]
    [].

Definition T : Value.t := M.run ltac:(M.monadic (
  M.call (| M.get_name (| globals, locals, "TypeVar" |), [Constant.str "T"] |))).

Definition FixedUint : Value.t :=
  builtins.make_klass
    [(globals, "int")]
    [

    ]
    [].

Definition U256 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_be_bytes",
        fun (args : list Value.t) (locals : nat) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| locals, [("cls", cls); ("buffer", buffer)] |) in
            let _ := Constant.str "
        Converts a sequence of bytes into a fixed sized unsigned integer
        from its big endian representation.
        " in
            let _ :=
              if M.is_true (Compare.gt (| M.call (| M.get_name (| globals, locals, "len" |), [M.get_name (| globals, locals, "buffer" |)] |), Constant.int 32 |)) then
(* At stmt: unsupported node type: Raise *)
              else
 in
            let _ := M.return_ (| M.call (| M.get_name (| globals, locals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, locals, "int" |), "from_bytes" |), [M.get_name (| globals, locals, "buffer" |); Constant.str "big"] |)] |) |) in
            M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "from_signed",
        fun (args : list Value.t) (locals : nat) =>
          match args with
          | [cls; value] => ltac:(M.monadic (
            let _ := M.set_locals (| locals, [("cls", cls); ("value", value)] |) in
            let _ := Constant.str "
        Creates an unsigned integer representing `value` using two's
        complement.
        " in
            let _ :=
              if M.is_true (Compare.gt_e (| M.get_name (| globals, locals, "value" |), Constant.int 0 |)) then
                let _ := M.return_ (| M.call (| M.get_name (| globals, locals, "cls" |), [M.get_name (| globals, locals, "value" |)] |) |) in
              else
 in
            let _ := M.return_ (| M.call (| M.get_name (| globals, locals, "cls" |), [BinOp.bit_and (| M.get_name (| globals, locals, "value" |), M.get_field (| M.get_name (| globals, locals, "cls" |), "MAX_VALUE" |) |)] |) |) in
            M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ]
    [].

(* At top_level_stmt: unsupported node type: Assign *)

Definition U32 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_le_bytes",
        fun (args : list Value.t) (locals : nat) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| locals, [("cls", cls); ("buffer", buffer)] |) in
            let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
            let _ :=
              if M.is_true (Compare.gt (| M.call (| M.get_name (| globals, locals, "len" |), [M.get_name (| globals, locals, "buffer" |)] |), Constant.int 4 |)) then
(* At stmt: unsupported node type: Raise *)
              else
 in
            let _ := M.return_ (| M.call (| M.get_name (| globals, locals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, locals, "int" |), "from_bytes" |), [M.get_name (| globals, locals, "buffer" |); Constant.str "little"] |)] |) |) in
            M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ]
    [].

(* At top_level_stmt: unsupported node type: Assign *)

Definition U64 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_le_bytes",
        fun (args : list Value.t) (locals : nat) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| locals, [("cls", cls); ("buffer", buffer)] |) in
            let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
            let _ :=
              if M.is_true (Compare.gt (| M.call (| M.get_name (| globals, locals, "len" |), [M.get_name (| globals, locals, "buffer" |)] |), Constant.int 8 |)) then
(* At stmt: unsupported node type: Raise *)
              else
 in
            let _ := M.return_ (| M.call (| M.get_name (| globals, locals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, locals, "int" |), "from_bytes" |), [M.get_name (| globals, locals, "buffer" |); Constant.str "little"] |)] |) |) in
            M.pure Constant.None_))
          | _ => M.impossible
          end
      );
      (
        "from_be_bytes",
        fun (args : list Value.t) (locals : nat) =>
          match args with
          | [cls; buffer] => ltac:(M.monadic (
            let _ := M.set_locals (| locals, [("cls", cls); ("buffer", buffer)] |) in
            let _ := Constant.str "
        Converts a sequence of bytes into an unsigned 64 bit integer from its
        big endian representation.
        " in
            let _ :=
              if M.is_true (Compare.gt (| M.call (| M.get_name (| globals, locals, "len" |), [M.get_name (| globals, locals, "buffer" |)] |), Constant.int 8 |)) then
(* At stmt: unsupported node type: Raise *)
              else
 in
            let _ := M.return_ (| M.call (| M.get_name (| globals, locals, "cls" |), [M.call (| M.get_field (| M.get_name (| globals, locals, "int" |), "from_bytes" |), [M.get_name (| globals, locals, "buffer" |); Constant.str "big"] |)] |) |) in
            M.pure Constant.None_))
          | _ => M.impossible
          end
      )
    ]
    [].

(* At top_level_stmt: unsupported node type: Assign *)

Definition B : Value.t := M.run ltac:(M.monadic (
  M.call (| M.get_name (| globals, locals, "TypeVar" |), [Constant.str "B"] |))).

Definition FixedBytes : Value.t :=
  builtins.make_klass
    [(globals, "bytes")]
    [

    ]
    [].

Definition Bytes0 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [].

Definition Bytes4 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [].

Definition Bytes8 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [].

Definition Bytes20 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [].

Definition Bytes32 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [].

Definition Bytes48 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [].

Definition Bytes64 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [].

Definition Bytes256 : Value.t :=
  builtins.make_klass
    [(globals, "FixedBytes")]
    [

    ]
    [].

Definition Bytes : Value.t := M.run ltac:(M.monadic (
  M.get_name (| globals, locals, "bytes" |))).

Definition expr_925 : Value.t :=
  Constant.str "
Sequence of bytes (octets) of arbitrary length.
".

Definition _setattr_function (args : list Value.t) : M :=
  match args with
  | [self; attr; value] => ltac:(M.monadic (
  let _ :=
    if M.is_true (M.call (| M.get_name (| globals, locals, "getattr" |), [M.get_name (| globals, locals, "self" |); Constant.str "_frozen"; Value.None] |)) then
(* At stmt: unsupported node type: Raise *)
    else
      let _ := M.call (| M.get_field (| M.get_name (| globals, locals, "object" |), "__setattr__" |), [M.get_name (| globals, locals, "self" |); M.get_name (| globals, locals, "attr" |); M.get_name (| globals, locals, "value" |)] |) in in))
  | _ => M.impossible
  end.

Definition _delattr_function (args : list Value.t) : M :=
  match args with
  | [self; attr] => ltac:(M.monadic (
  let _ :=
    if M.is_true (M.get_field (| M.get_name (| globals, locals, "self" |), "_frozen" |)) then
(* At stmt: unsupported node type: Raise *)
    else
      let _ := M.call (| M.get_field (| M.get_name (| globals, locals, "object" |), "__delattr__" |), [M.get_name (| globals, locals, "self" |); M.get_name (| globals, locals, "attr" |)] |) in in))
  | _ => M.impossible
  end.

Definition _make_init_function (args : list Value.t) : M :=
  match args with
  | [f] => ltac:(M.monadic (
(* At stmt: unsupported node type: FunctionDef *)
  let _ := M.return_ (| M.get_name (| globals, locals, "init_function" |) |) in))
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
    M.get_field (| M.get_name (| globals, locals, "cls" |), "__slots__" |),
    BinOp.add (| (Constant.str "_frozen"), M.call (| M.get_name (| globals, locals, "tuple" |), [M.get_field (| M.get_name (| globals, locals, "cls" |), "__annotations__" |)] |) |)
  |) in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, locals, "cls" |), "__init__" |),
    M.call (| M.get_name (| globals, locals, "_make_init_function" |), [M.get_field (| M.get_name (| globals, locals, "cls" |), "__init__" |)] |)
  |) in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, locals, "cls" |), "__setattr__" |),
    M.get_name (| globals, locals, "_setattr_function" |)
  |) in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, locals, "cls" |), "__delattr__" |),
    M.get_name (| globals, locals, "_delattr_function" |)
  |) in
  let _ := M.return_ (| M.call (| M.call (| M.get_name (| globals, locals, "type" |), [M.get_name (| globals, locals, "cls" |)] |), [M.get_field (| M.get_name (| globals, locals, "cls" |), "__name__" |); M.get_field (| M.get_name (| globals, locals, "cls" |), "__bases__" |); M.call (| M.get_name (| globals, locals, "dict" |), [M.get_field (| M.get_name (| globals, locals, "cls" |), "__dict__" |)] |)] |) |) in))
  | _ => M.impossible
  end.

Definition S : Value.t := M.run ltac:(M.monadic (
  M.call (| M.get_name (| globals, locals, "TypeVar" |), [Constant.str "S"] |))).

Definition modify (args : list Value.t) : M :=
  match args with
  | [obj; f] => ltac:(M.monadic (
  let _ := Constant.str "
    Create a copy of `obj` (which must be [`@slotted_freezable`]), and modify
    it by applying `f`. The returned copy will be frozen.

    [`@slotted_freezable`]: ref:ethereum.base_types.slotted_freezable
    " in
  let _ := M.assert (| M.call (| M.get_name (| globals, locals, "is_dataclass" |), [M.get_name (| globals, locals, "obj" |)] |) |) in
  let _ := M.assert (| M.call (| M.get_name (| globals, locals, "isinstance" |), [M.get_name (| globals, locals, "obj" |); M.get_name (| globals, locals, "SlottedFreezable" |)] |) |) in
  let new_obj := M.call (| M.get_name (| globals, locals, "replace" |), [M.get_name (| globals, locals, "obj" |)] |) in
  let _ := M.call (| M.get_name (| globals, locals, "f" |), [M.get_name (| globals, locals, "new_obj" |)] |) in
  let _ := M.assign (|
    M.get_field (| M.get_name (| globals, locals, "new_obj" |), "_frozen" |),
    Constant.bool true
  |) in
  let _ := M.return_ (| M.get_name (| globals, locals, "new_obj" |) |) in))
  | _ => M.impossible
  end.
