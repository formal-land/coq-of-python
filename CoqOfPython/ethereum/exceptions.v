Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "ethereum.exceptions".

Definition locals_stack : list Locals.t := [].

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

Definition EthereumException : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "Exception")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition InvalidBlock : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "EthereumException")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition RLPDecodingError : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "InvalidBlock")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.

Definition RLPEncodingError : Value.t := builtins.make_klass {|
  Klass.bases := [
    (globals, "EthereumException")
  ];
  Klass.class_methods := [
  ];
  Klass.methods := [
  ];
|}.
