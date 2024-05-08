Require Import CoqOfPython.CoqOfPython.

Definition expr_1 : Value.t :=
  (Value.String "
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
").

Module import_dataclasses.
  Require Import dataclasses.
  Definition is_dataclass := is_dataclass.
  Definition replace := replace.
End import_dataclasses.
Import import_dataclasses.

Module import_typing.
  Require Import typing.
  Definition Any := Any.
  Definition Callable := Callable.
  Definition ClassVar := ClassVar.
  Definition Optional := Optional.
  Definition Protocol := Protocol.
  Definition Tuple := Tuple.
  Definition Type_ := Type_.
  Definition TypeVar := TypeVar.
  Definition runtime_checkable := runtime_checkable.
End import_typing.
Import import_typing.

(* At top_level_stmt: unsupported node type: ClassDef *)

let U255_CEIL_VALUE := (BinOp.Pow (Value.Integer 2) (Value.Integer 255)) in

Definition expr_50 : Value.t :=
  (Value.String "
Smallest value that requires 256 bits to represent. Mostly used in signed
arithmetic operations, like [`sdiv`].

[`sdiv`]: ref:ethereum.frontier.vm.instructions.arithmetic.sdiv
").

let U256_CEIL_VALUE := (BinOp.Pow (Value.Integer 2) (Value.Integer 256)) in

Definition expr_58 : Value.t :=
  (Value.String "
Smallest value that requires 257 bits to represent. Used when converting a
[`U256`] in two's complement format to a regular `int` in [`U256.to_signed`].

[`U256`]: ref:ethereum.base_types.U256
[`U256.to_signed`]: ref:ethereum.base_types.U256.to_signed
").

(* At top_level_stmt: unsupported node type: ClassDef *)

let T := (M.call (| TypeVar, [(Value.String "T")] |)) in

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

let _ := M.assign (|
U256.MAX_VALUE,
(M.call (| int.__new__, [U256; (BinOp.Sub (BinOp.Pow (Value.Integer 2) (Value.Integer 256)) (Value.Integer 1))] |))
|) in

(* At top_level_stmt: unsupported node type: ClassDef *)

let _ := M.assign (|
U32.MAX_VALUE,
(M.call (| int.__new__, [U32; (BinOp.Sub (BinOp.Pow (Value.Integer 2) (Value.Integer 32)) (Value.Integer 1))] |))
|) in

(* At top_level_stmt: unsupported node type: ClassDef *)

let _ := M.assign (|
U64.MAX_VALUE,
(M.call (| int.__new__, [U64; (BinOp.Sub (BinOp.Pow (Value.Integer 2) (Value.Integer 64)) (Value.Integer 1))] |))
|) in

let B := (M.call (| TypeVar, [(Value.String "B")] |)) in

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

(* At top_level_stmt: unsupported node type: ClassDef *)

let Bytes := bytes in

Definition expr_925 : Value.t :=
  (Value.String "
Sequence of bytes (octets) of arbitrary length.
").

Definition _setattr_function (args : list Value.t) : M :=
  match args with
  | [self; attr; value] => ltac:(M.monadic (
  let _ :=
    if M.is_true (M.call (| getattr, [self; (Value.String "_frozen"); (Value.None)] |)) then
(* At stmt: unsupported node type: Raise *)
    else
      let _ := (M.call (| object.__setattr__, [self; attr; value] |)) in in))
  | _ => M.impossible
  end.

Definition _delattr_function (args : list Value.t) : M :=
  match args with
  | [self; attr] => ltac:(M.monadic (
  let _ :=
    if M.is_true self._frozen then
(* At stmt: unsupported node type: Raise *)
    else
      let _ := (M.call (| object.__delattr__, [self; attr] |)) in in))
  | _ => M.impossible
  end.

Definition _make_init_function (args : list Value.t) : M :=
  match args with
  | [f] => ltac:(M.monadic (
(* At stmt: unsupported node type: FunctionDef *)
  let _ := M.return (| init_function |) in))
  | _ => M.impossible
  end.

Definition slotted_freezable (args : list Value.t) : M :=
  match args with
  | [cls] => ltac:(M.monadic (
  let _ := (Value.String "
    Monkey patches a dataclass so it can be frozen by setting `_frozen` to
    `True` and uses `__slots__` for efficiency.

    Instances will be created frozen by default unless you pass `_frozen=False`
    to `__init__`.
    ") in
  let _ := M.assign (|
    cls.__slots__,
    (BinOp.Add ((Value.String "_frozen")) (M.call (| tuple, [cls.__annotations__] |)))
  |) in
  let _ := M.assign (|
    cls.__init__,
    (M.call (| _make_init_function, [cls.__init__] |))
  |) in
  let _ := M.assign (|
    cls.__setattr__,
    _setattr_function
  |) in
  let _ := M.assign (|
    cls.__delattr__,
    _delattr_function
  |) in
  let _ := M.return (| (M.call (| (M.call (| type, [cls] |)), [cls.__name__; cls.__bases__; (M.call (| dict, [cls.__dict__] |))] |)) |) in))
  | _ => M.impossible
  end.

let S := (M.call (| TypeVar, [(Value.String "S")] |)) in

Definition modify (args : list Value.t) : M :=
  match args with
  | [obj; f] => ltac:(M.monadic (
  let _ := (Value.String "
    Create a copy of `obj` (which must be [`@slotted_freezable`]), and modify
    it by applying `f`. The returned copy will be frozen.

    [`@slotted_freezable`]: ref:ethereum.base_types.slotted_freezable
    ") in
  let _ := M.assert (| (M.call (| is_dataclass, [obj] |)) |) in
  let _ := M.assert (| (M.call (| isinstance, [obj; SlottedFreezable] |)) |) in
  let new_obj := (M.call (| replace, [obj] |)) in
  let _ := (M.call (| f, [new_obj] |)) in
  let _ := M.assign (|
    new_obj._frozen,
    (Value.Bool true)
  |) in
  let _ := M.return (| new_obj |) in))
  | _ => M.impossible
  end.
