Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
### Introduction

Seeing as internet connections have been vastly expanding across the
world, spreading information has become as cheap as ever. Bitcoin, for
example, has demonstrated the possibility of creating a decentralized,
trade system that is accessible around the world. Namecoin is another
system that built off of Bitcoin's currency structure to create other
simple technological applications.

Ethereum's goal is to create a cryptographically secure system in which
any and all types of transaction-based concepts can be built. It provides
an exceptionally accessible and decentralized system to build software
and execute transactions.

This package contains a reference implementation, written as simply as
possible, to aid in defining the behavior of Ethereum clients.
".

(* At top_level_stmt: unsupported node type: Import *)

Definition __version__ : Value.t := M.run ltac:(M.monadic (
  Constant.str "0.1.0"
)).

Definition EVM_RECURSION_LIMIT : Value.t := M.run ltac:(M.monadic (
  BinOp.mult (|
    Constant.int 1024,
    Constant.int 12
  |)
)).

Definition expr_27 : Value.t :=
  M.call (|
    M.get_field (| M.get_name (| globals, "sys" |), "setrecursionlimit" |),
    make_list [
      M.call (|
        M.get_name (| globals, "max" |),
        make_list [
          M.get_name (| globals, "EVM_RECURSION_LIMIT" |);
          M.call (|
            M.get_field (| M.get_name (| globals, "sys" |), "getrecursionlimit" |),
            make_list [],
            make_dict []
          |)
        ],
        make_dict []
      |)
    ],
    make_dict []
  |).
