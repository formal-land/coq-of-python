Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Precompiled Contract Addresses
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Mapping of precompiled contracts their implementations.
".

Require typing.
Axiom typing_Callable :
  IsGlobalAlias globals typing.globals "Callable".
Axiom typing_Dict :
  IsGlobalAlias globals typing.globals "Dict".

Require fork_types.
Axiom fork_types_Address :
  IsGlobalAlias globals fork_types.globals "Address".

Require __init__.
Axiom __init___ECRECOVER_ADDRESS :
  IsGlobalAlias globals __init__.globals "ECRECOVER_ADDRESS".
Axiom __init___IDENTITY_ADDRESS :
  IsGlobalAlias globals __init__.globals "IDENTITY_ADDRESS".
Axiom __init___RIPEMD160_ADDRESS :
  IsGlobalAlias globals __init__.globals "RIPEMD160_ADDRESS".
Axiom __init___SHA256_ADDRESS :
  IsGlobalAlias globals __init__.globals "SHA256_ADDRESS".

Require ecrecover.
Axiom ecrecover_ecrecover :
  IsGlobalAlias globals ecrecover.globals "ecrecover".

Require identity.
Axiom identity_identity :
  IsGlobalAlias globals identity.globals "identity".

Require ripemd160.
Axiom ripemd160_ripemd160 :
  IsGlobalAlias globals ripemd160.globals "ripemd160".

Require sha256.
Axiom sha256_sha256 :
  IsGlobalAlias globals sha256.globals "sha256".

(* At top_level_stmt: unsupported node type: AnnAssign *)
