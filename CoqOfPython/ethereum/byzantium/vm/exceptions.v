Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.byzantium.vm.exceptions".

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Exceptions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Exceptions which cause the EVM to halt exceptionally.
".

Axiom ethereum_exceptions_imports :
  AreImported globals "ethereum.exceptions" [ "EthereumException" ].

Definition ExceptionalHalt : Value.t :=
  builtins.make_klass
    [(globals, "EthereumException")]
    [

    ]
    [

    ].

Definition Revert : Value.t :=
  builtins.make_klass
    [(globals, "EthereumException")]
    [

    ]
    [

    ].

Definition StackUnderflowError : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [

    ].

Definition StackOverflowError : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [

    ].

Definition OutOfGasError : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [

    ].

Definition InvalidOpcode : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [
      (
        "__init__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "code" ] |) in
          let _ := M.call (|
    M.get_field (| M.call (|
      M.get_name (| globals, "super" |),
      make_list [],
      make_dict []
    |), "__init__" |),
    make_list [
      M.get_name (| globals, "code" |)
    ],
    make_dict []
  |) in
          let _ := M.assign (|
            M.get_field (| M.get_name (| globals, "self" |), "code" |),
            M.get_name (| globals, "code" |)
          |) in
          M.pure Constant.None_))
      )
    ].

Definition InvalidJumpDestError : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [

    ].

Definition StackDepthLimitError : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [

    ].

Definition WriteInStaticContext : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [

    ].

Definition OutOfBoundsRead : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [

    ].

Definition AddressCollision : Value.t :=
  builtins.make_klass
    [(globals, "ExceptionalHalt")]
    [

    ]
    [

    ].
