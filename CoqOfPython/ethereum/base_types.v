Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  (Constant.str "
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
  make_klass
    [(globals, "Protocol")]
    []
    [].

Definition U255_CEIL_VALUE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (| (Constant.int 2), (Constant.int 255) |))).

Definition expr_50 : Value.t :=
  (Constant.str "
Smallest value that requires 256 bits to represent. Mostly used in signed
arithmetic operations, like [`sdiv`].

[`sdiv`]: ref:ethereum.frontier.vm.instructions.arithmetic.sdiv
").

Definition U256_CEIL_VALUE : Value.t := M.run ltac:(M.monadic (
  BinOp.pow (| (Constant.int 2), (Constant.int 256) |))).

Definition expr_58 : Value.t :=
  (Constant.str "
Smallest value that requires 257 bits to represent. Used when converting a
[`U256`] in two's complement format to a regular `int` in [`U256.to_signed`].

[`U256`]: ref:ethereum.base_types.U256
[`U256.to_signed`]: ref:ethereum.base_types.U256.to_signed
").

Definition Uint : Value.t :=
  make_klass
    [(globals, "int")]
    ["from_be_bytes"; "from_le_bytes"]
    [].

Definition T : Value.t := M.run ltac:(M.monadic (
  (M.call (| TypeVar, [(Constant.str "T")] |)))).

Definition FixedUint : Value.t :=
  make_klass
    [(globals, "int")]
    []
    [].

Definition U256 : Value.t :=
  make_klass
    [(globals, "FixedUint")]
    ["from_be_bytes"; "from_signed"]
    [].

(* At top_level_stmt: unsupported node type: Assign *)

Definition U32 : Value.t :=
  make_klass
    [(globals, "FixedUint")]
    ["from_le_bytes"]
    [].

(* At top_level_stmt: unsupported node type: Assign *)

Definition U64 : Value.t :=
  make_klass
    [(globals, "FixedUint")]
    ["from_le_bytes"; "from_be_bytes"]
    [].

(* At top_level_stmt: unsupported node type: Assign *)

Definition B : Value.t := M.run ltac:(M.monadic (
  (M.call (| TypeVar, [(Constant.str "B")] |)))).

Definition FixedBytes : Value.t :=
  make_klass
    [(globals, "bytes")]
    []
    [].

Definition Bytes0 : Value.t :=
  make_klass
    [(globals, "FixedBytes")]
    []
    [].

Definition Bytes4 : Value.t :=
  make_klass
    [(globals, "FixedBytes")]
    []
    [].

Definition Bytes8 : Value.t :=
  make_klass
    [(globals, "FixedBytes")]
    []
    [].

Definition Bytes20 : Value.t :=
  make_klass
    [(globals, "FixedBytes")]
    []
    [].

Definition Bytes32 : Value.t :=
  make_klass
    [(globals, "FixedBytes")]
    []
    [].

Definition Bytes48 : Value.t :=
  make_klass
    [(globals, "FixedBytes")]
    []
    [].

Definition Bytes64 : Value.t :=
  make_klass
    [(globals, "FixedBytes")]
    []
    [].

Definition Bytes256 : Value.t :=
  make_klass
    [(globals, "FixedBytes")]
    []
    [].

Definition Bytes : Value.t := M.run ltac:(M.monadic (
  bytes)).

Definition expr_925 : Value.t :=
  (Constant.str "
Sequence of bytes (octets) of arbitrary length.
").

Definition _setattr_function (args : list Value.t) : M :=
  match args with
  | [self; attr; value] => ltac:(M.monadic (
  let _ :=
    if M.is_true (M.call (| getattr, [self; (Constant.str "_frozen"); (Value.None)] |)) then
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
  let _ := (Constant.str "
    Monkey patches a dataclass so it can be frozen by setting `_frozen` to
    `True` and uses `__slots__` for efficiency.

    Instances will be created frozen by default unless you pass `_frozen=False`
    to `__init__`.
    ") in
  let _ := M.assign (|
    cls.__slots__,
    BinOp.add (| ((Constant.str "_frozen")), (M.call (| tuple, [cls.__annotations__] |)) |)
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

Definition S : Value.t := M.run ltac:(M.monadic (
  (M.call (| TypeVar, [(Constant.str "S")] |)))).

Definition modify (args : list Value.t) : M :=
  match args with
  | [obj; f] => ltac:(M.monadic (
  let _ := (Constant.str "
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
    (Constant.bool true)
  |) in
  let _ := M.return (| new_obj |) in))
  | _ => M.impossible
  end.
