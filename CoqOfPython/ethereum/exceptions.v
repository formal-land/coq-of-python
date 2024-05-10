Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.exceptions".

Definition expr_1 : Value.t :=
  Constant.str "
Exceptions
^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

The Ethereum specification exception classes.
".

Definition EthereumException : Value.t :=
  builtins.make_klass
    [(globals, "Exception")]
    [

    ]
    [

    ].

Definition InvalidBlock : Value.t :=
  builtins.make_klass
    [(globals, "EthereumException")]
    [

    ]
    [

    ].

Definition RLPDecodingError : Value.t :=
  builtins.make_klass
    [(globals, "InvalidBlock")]
    [

    ]
    [

    ].

Definition RLPEncodingError : Value.t :=
  builtins.make_klass
    [(globals, "EthereumException")]
    [

    ]
    [

    ].
