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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "buffer" ] |) in
          let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its big endian representation.
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
          M.pure Constant.None_))
      );
      (
        "from_le_bytes",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "buffer" ] |) in
          let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "cls" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |),
                  make_list [
                    M.get_name (| globals, "buffer" |);
                    Constant.str "little"
                  ],
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
        "__init__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "value" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
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
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
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
          M.pure Constant.None_))
      );
      (
        "__sub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
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
          M.pure Constant.None_))
      );
      (
        "__rsub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
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
          M.pure Constant.None_))
      );
      (
        "__isub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__sub__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__mul__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
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
          M.pure Constant.None_))
      );
      (
        "__floordiv__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__floordiv__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rfloordiv__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rfloordiv__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__ifloordiv__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__floordiv__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__mod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__mod__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rmod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rmod__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__imod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__mod__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__divmod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let result :=
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__divmod__" |),
              make_list [
                M.get_name (| globals, "self" |);
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |) in
          let _ := M.return_ (|
            make_tuple [ M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 0 |)
              ],
              make_dict []
            |); M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 1 |)
              ],
              make_dict []
            |) ]
          M.pure Constant.None_))
      );
      (
        "__rdivmod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let result :=
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__rdivmod__" |),
              make_list [
                M.get_name (| globals, "self" |);
                M.get_name (| globals, "left" |)
              ],
              make_dict []
            |) in
          let _ := M.return_ (|
            make_tuple [ M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 0 |)
              ],
              make_dict []
            |); M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 1 |)
              ],
              make_dict []
            |) ]
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right"; "modulo" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__pow__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |);
                    M.get_name (| globals, "modulo" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rpow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left"; "modulo" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rpow__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |);
                    M.get_name (| globals, "modulo" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__ipow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right"; "modulo" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__pow__" |),
              make_list [
                M.get_name (| globals, "right" |);
                M.get_name (| globals, "modulo" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__xor__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__xor__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rxor__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rxor__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__ixor__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__xor__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "to_be_bytes32",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its big endian
        representation with exactly 32 bytes.
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
          M.pure Constant.None_))
      );
      (
        "to_be_bytes",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its big endian
        representation, without padding.
        " in
          let bit_length :=
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "bit_length" |),
              make_list [],
              make_dict []
            |) in
          let byte_length :=
            BinOp.floor_div (|
              BinOp.add (|
                M.get_name (| globals, "bit_length" |),
                Constant.int 7
              |),
              Constant.int 8
            |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, "byte_length" |);
                Constant.str "big"
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "to_le_bytes",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "number_bytes" ] |) in
          let _ := Constant.str "
        Converts this arbitrarily sized unsigned integer into its little endian
        representation, without padding.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, "number_bytes" |);
                Constant.str "little"
              ],
              make_dict []
            |)
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

Definition FixedUint : Value.t :=
  builtins.make_klass
    [(globals, "int")]
    [

    ]
    [
      (
        "__init__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "value" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
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
          M.pure Constant.None_))
      );
      (
        "__add__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let result :=
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__add__" |),
              make_list [
                M.get_name (| globals, "self" |);
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_name (| globals, "result" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "wrapping_add",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := Constant.str "
        Return a new instance containing `self + right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "int" |), "__add__" |),
                    make_list [
                      M.get_name (| globals, "self" |);
                      M.get_name (| globals, "right" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
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
          M.pure Constant.None_))
      );
      (
        "__sub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
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
          M.pure Constant.None_))
      );
      (
        "wrapping_sub",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := Constant.str "
        Return a new instance containing `self - right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "int" |), "__sub__" |),
                    make_list [
                      M.get_name (| globals, "self" |);
                      M.get_name (| globals, "right" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rsub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
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
          M.pure Constant.None_))
      );
      (
        "__isub__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__sub__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__mul__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let result :=
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__mul__" |),
              make_list [
                M.get_name (| globals, "self" |);
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_name (| globals, "result" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "wrapping_mul",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := Constant.str "
        Return a new instance containing `self * right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "int" |), "__mul__" |),
                    make_list [
                      M.get_name (| globals, "self" |);
                      M.get_name (| globals, "right" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
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
          M.pure Constant.None_))
      );
      (
        "__floordiv__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__floordiv__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rfloordiv__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rfloordiv__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__ifloordiv__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__floordiv__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__mod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__mod__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rmod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rmod__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__imod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__mod__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__divmod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let result :=
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, "super" |),
                make_list [
                  M.get_name (| globals, "FixedUint" |);
                  M.get_name (| globals, "self" |)
                ],
                make_dict []
              |), "__divmod__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |) in
          let _ := M.return_ (|
            make_tuple [ M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 0 |)
              ],
              make_dict []
            |); M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 1 |)
              ],
              make_dict []
            |) ]
          M.pure Constant.None_))
      );
      (
        "__rdivmod__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let result :=
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, "super" |),
                make_list [
                  M.get_name (| globals, "FixedUint" |);
                  M.get_name (| globals, "self" |)
                ],
                make_dict []
              |), "__rdivmod__" |),
              make_list [
                M.get_name (| globals, "left" |)
              ],
              make_dict []
            |) in
          let _ := M.return_ (|
            make_tuple [ M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 0 |)
              ],
              make_dict []
            |); M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_subscript (| M.get_name (| globals, "result" |), Constant.int 1 |)
              ],
              make_dict []
            |) ]
          M.pure Constant.None_))
      );
      (
        "__pow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right"; "modulo" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let result :=
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__pow__" |),
              make_list [
                M.get_name (| globals, "self" |);
                M.get_name (| globals, "right" |);
                M.get_name (| globals, "modulo" |)
              ],
              make_dict []
            |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.get_name (| globals, "result" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "wrapping_pow",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right"; "modulo" ] |) in
          let _ := Constant.str "
        Return a new instance containing `self ** right (mod modulo)`.

        If omitted, `modulo` defaults to `Uint(self.MAX_VALUE) + 1`.

        Passing a `right` or `modulo` value greater than [`MAX_VALUE`] or
        less than zero will raise a `ValueError`, even if the result would fit
        in this integer type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "int" |), "__pow__" |),
                    make_list [
                      M.get_name (| globals, "self" |);
                      M.get_name (| globals, "right" |);
                      M.get_name (| globals, "modulo" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rpow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left"; "modulo" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rpow__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |);
                    M.get_name (| globals, "modulo" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__ipow__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right"; "modulo" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__pow__" |),
              make_list [
                M.get_name (| globals, "right" |);
                M.get_name (| globals, "modulo" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__and__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__and__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__or__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__or__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__xor__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__xor__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "right" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rxor__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "left" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rxor__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "left" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__ixor__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "right" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "__xor__" |),
              make_list [
                M.get_name (| globals, "right" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__invert__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                BinOp.bit_and (|
                  M.call (|
                    M.get_field (| M.get_name (| globals, "int" |), "__invert__" |),
                    make_list [
                      M.get_name (| globals, "self" |)
                    ],
                    make_dict []
                  |),
                  M.get_field (| M.get_name (| globals, "self" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "__rshift__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "shift_by" ] |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "int" |), "__new__" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "__class__" |);
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "__rshift__" |),
                  make_list [
                    M.get_name (| globals, "self" |);
                    M.get_name (| globals, "shift_by" |)
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "to_be_bytes",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Converts this unsigned integer into its big endian representation,
        omitting leading zero bytes.
        " in
          let bit_length :=
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "bit_length" |),
              make_list [],
              make_dict []
            |) in
          let byte_length :=
            BinOp.floor_div (|
              BinOp.add (|
                M.get_name (| globals, "bit_length" |),
                Constant.int 7
              |),
              Constant.int 8
            |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, "byte_length" |);
                Constant.str "big"
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      )
    ].

Definition U256 : Value.t :=
  builtins.make_klass
    [(globals, "FixedUint")]
    [
      (
        "from_be_bytes",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "buffer" ] |) in
          let _ := Constant.str "
        Converts a sequence of bytes into a fixed sized unsigned integer
        from its big endian representation.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
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
          M.pure Constant.None_))
      );
      (
        "from_signed",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "value" ] |) in
          let _ := Constant.str "
        Creates an unsigned integer representing `value` using two's
        complement.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "cls" |),
              make_list [
                BinOp.bit_and (|
                  M.get_name (| globals, "value" |),
                  M.get_field (| M.get_name (| globals, "cls" |), "MAX_VALUE" |)
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      )
    ]
    [
      (
        "to_be_bytes32",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Converts this 256-bit unsigned integer into its big endian
        representation with exactly 32 bytes.
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
          M.pure Constant.None_))
      );
      (
        "to_signed",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Decodes a signed integer from its two's complement representation.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            BinOp.sub (|
              M.call (|
                M.get_name (| globals, "int" |),
                make_list [
                  M.get_name (| globals, "self" |)
                ],
                make_dict []
              |),
              M.get_name (| globals, "U256_CEIL_VALUE" |)
            |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "buffer" ] |) in
          let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "cls" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |),
                  make_list [
                    M.get_name (| globals, "buffer" |);
                    Constant.str "little"
                  ],
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
        "to_le_bytes4",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, with exactly 4 bytes.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "Bytes4" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |),
                  make_list [
                    Constant.int 4;
                    Constant.str "little"
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "to_le_bytes",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, in the fewest bytes possible.
        " in
          let bit_length :=
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "bit_length" |),
              make_list [],
              make_dict []
            |) in
          let byte_length :=
            BinOp.floor_div (|
              BinOp.add (|
                M.get_name (| globals, "bit_length" |),
                Constant.int 7
              |),
              Constant.int 8
            |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, "byte_length" |);
                Constant.str "little"
              ],
              make_dict []
            |)
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "buffer" ] |) in
          let _ := Constant.str "
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "cls" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, "int" |), "from_bytes" |),
                  make_list [
                    M.get_name (| globals, "buffer" |);
                    Constant.str "little"
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "from_be_bytes",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls"; "buffer" ] |) in
          let _ := Constant.str "
        Converts a sequence of bytes into an unsigned 64 bit integer from its
        big endian representation.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
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
          M.pure Constant.None_))
      )
    ]
    [
      (
        "to_le_bytes8",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, with exactly 8 bytes.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "Bytes8" |),
              make_list [
                M.call (|
                  M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |),
                  make_list [
                    Constant.int 8;
                    Constant.str "little"
                  ],
                  make_dict []
                |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      );
      (
        "to_le_bytes",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        Converts this fixed sized unsigned integer into its little endian
        representation, in the fewest bytes possible.
        " in
          let bit_length :=
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "bit_length" |),
              make_list [],
              make_dict []
            |) in
          let byte_length :=
            BinOp.floor_div (|
              BinOp.add (|
                M.get_name (| globals, "bit_length" |),
                Constant.int 7
              |),
              Constant.int 8
            |) in
          let _ := M.return_ (|
            M.call (|
              M.get_field (| M.get_name (| globals, "self" |), "to_bytes" |),
              make_list [
                M.get_name (| globals, "byte_length" |);
                Constant.str "little"
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      )
    ].

(* At top_level_stmt: unsupported node type: Assign *)

Definition B : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
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
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "cls" ] |) in
          let _ := Constant.str "
        Create a new instance, ensuring the result has the correct length.
        " in
          let x :=
            make_list_concat (| [
              make_list [
                Constant.int 1;
                Constant.int 2
              ];
              make_list [
                Constant.str "x";
                Constant.str "y";
                Constant.str "z"
              ];
              make_list [
                Constant.int 3
              ]
            ] |) in
          let result :=
            M.call (|
              M.get_field (| M.call (|
                M.get_name (| globals, "super" |),
                make_list [
                  M.get_name (| globals, "FixedBytes" |);
                  M.get_name (| globals, "cls" |)
                ],
                make_dict []
              |), "__new__" |),
              make_list_concat (| [
                make_list [
                  M.get_name (| globals, "cls" |)
                ];
                M.get_name (| globals, "args" |)
              ] |),
              make_dict []
            |) in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.get_name (| globals, "result" |)
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
  M.get_name (| globals, "bytes" |)
)).

Definition expr_926 : Value.t :=
  Constant.str "
Sequence of bytes (octets) of arbitrary length.
".

Definition _setattr_function : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "self"; "attr"; "value" ] |) in
    let _ :=
        let _ := M.call (|
    M.get_field (| M.get_name (| globals, "object" |), "__setattr__" |),
    make_list [
      M.get_name (| globals, "self" |);
      M.get_name (| globals, "attr" |);
      M.get_name (| globals, "value" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition _delattr_function : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "self"; "attr" ] |) in
    let _ :=
        let _ := M.call (|
    M.get_field (| M.get_name (| globals, "object" |), "__delattr__" |),
    make_list [
      M.get_name (| globals, "self" |);
      M.get_name (| globals, "attr" |)
    ],
    make_dict []
  |) in
        M.pure Constant.None_
      )) |) in
    M.pure Constant.None_)).

Definition _make_init_function : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "f" ] |) in
(* At stmt: unsupported node type: FunctionDef *)
    let _ := M.return_ (|
      M.get_name (| globals, "init_function" |)
    M.pure Constant.None_)).

Definition slotted_freezable : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "cls" ] |) in
    let _ := Constant.str "
    Monkey patches a dataclass so it can be frozen by setting `_frozen` to
    `True` and uses `__slots__` for efficiency.

    Instances will be created frozen by default unless you pass `_frozen=False`
    to `__init__`.
    " in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "cls" |), "__slots__" |),
      BinOp.add (|
        make_tuple [ Constant.str "_frozen" ],
        M.call (|
          M.get_name (| globals, "tuple" |),
          make_list [
            M.get_field (| M.get_name (| globals, "cls" |), "__annotations__" |)
          ],
          make_dict []
        |)
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "cls" |), "__init__" |),
      M.call (|
        M.get_name (| globals, "_make_init_function" |),
        make_list [
          M.get_field (| M.get_name (| globals, "cls" |), "__init__" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "cls" |), "__setattr__" |),
      M.get_name (| globals, "_setattr_function" |)
    |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "cls" |), "__delattr__" |),
      M.get_name (| globals, "_delattr_function" |)
    |) in
    let _ := M.return_ (|
      M.call (|
        M.call (|
          M.get_name (| globals, "type" |),
          make_list [
            M.get_name (| globals, "cls" |)
          ],
          make_dict []
        |),
        make_list [
          M.get_field (| M.get_name (| globals, "cls" |), "__name__" |);
          M.get_field (| M.get_name (| globals, "cls" |), "__bases__" |);
          M.call (|
            M.get_name (| globals, "dict" |),
            make_list [
              M.get_field (| M.get_name (| globals, "cls" |), "__dict__" |)
            ],
            make_dict []
          |)
        ],
        make_dict []
      |)
    M.pure Constant.None_)).

Definition S : Value.t := M.run ltac:(M.monadic (
  M.call (|
    M.get_name (| globals, "TypeVar" |),
    make_list [
      Constant.str "S"
    ],
    make_dict []
  |)
)).

Definition modify : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "obj"; "f" ] |) in
    let _ := Constant.str "
    Create a copy of `obj` (which must be [`@slotted_freezable`]), and modify
    it by applying `f`. The returned copy will be frozen.

    [`@slotted_freezable`]: ref:ethereum.base_types.slotted_freezable
    " in
    let _ := M.assert (| M.call (|
    M.get_name (| globals, "is_dataclass" |),
    make_list [
      M.get_name (| globals, "obj" |)
    ],
    make_dict []
  |) |) in
    let _ := M.assert (| M.call (|
    M.get_name (| globals, "isinstance" |),
    make_list [
      M.get_name (| globals, "obj" |);
      M.get_name (| globals, "SlottedFreezable" |)
    ],
    make_dict []
  |) |) in
    let new_obj :=
      M.call (|
        M.get_name (| globals, "replace" |),
        make_list [
          M.get_name (| globals, "obj" |)
        ],
        make_dict []
      |) in
    let _ := M.call (|
    M.get_name (| globals, "f" |),
    make_list [
      M.get_name (| globals, "new_obj" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "new_obj" |), "_frozen" |),
      Constant.bool true
    |) in
    let _ := M.return_ (|
      M.get_name (| globals, "new_obj" |)
    M.pure Constant.None_)).
