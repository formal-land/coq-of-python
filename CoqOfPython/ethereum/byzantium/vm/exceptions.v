Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.byzantium.vm.exceptions".

Definition locals_stack : list Locals.t := [].

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

Axiom ethereum_exceptions_imports_EthereumException :
  IsImported globals "ethereum.exceptions" "EthereumException".

Definition ExceptionalHalt : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "EthereumException")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition Revert : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "EthereumException")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition StackUnderflowError : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition StackOverflowError : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition OutOfGasError : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition InvalidOpcode : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
    (
      "__init__",
      fun (args kwargs : Value.t) =>
        let- locals_stack := M.create_locals locals_stack args kwargs [ "self"; "code" ] in
        ltac:(M.monadic (
        let _ := M.call (|
    M.get_field (| M.call (|
      M.get_name (| globals, locals_stack, "super" |),
      make_list [],
      make_dict []
    |), "__init__" |),
    make_list [
      M.get_name (| globals, locals_stack, "code" |)
    ],
    make_dict []
  |) in
        let _ := M.assign (|
          M.get_field (| M.get_name (| globals, locals_stack, "self" |), "code" |),
          M.get_name (| globals, locals_stack, "code" |)
        |) in
        M.pure Constant.None_))
    )
  ]
|}.

Definition InvalidJumpDestError : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition StackDepthLimitError : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition WriteInStaticContext : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition OutOfBoundsRead : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.

Definition AddressCollision : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "ExceptionalHalt")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ]
|}.
