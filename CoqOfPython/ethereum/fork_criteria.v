Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Fork Criteria
^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Classes for specifying criteria for Mainnet forks.
".

(* At top_level_stmt: unsupported node type: Import *)

Require abc.
Axiom abc_ABC :
  IsGlobalAlias globals abc.globals "ABC".
Axiom abc_abstractmethod :
  IsGlobalAlias globals abc.globals "abstractmethod".

Require typing.
Axiom typing_Final :
  IsGlobalAlias globals typing.globals "Final".
Axiom typing_Tuple :
  IsGlobalAlias globals typing.globals "Tuple".

Definition ForkCriteria : Value.t :=
  builtins.make_klass
    [(globals, "ABC")]
    [

    ]
    [
      (
        "__eq__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "other" ] |) in
          let _ := Constant.str "
        Equality for fork criteria.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.get_name (| globals, "NotImplemented" |)
          M.pure Constant.None_))
      );
      (
        "__lt__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "other" ] |) in
          let _ := Constant.str "
        Ordering for fork criteria. Block number forks are before timestamp
        forks and scheduled forks are before unscheduled forks.
        " in
          let _ :=
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.get_name (| globals, "NotImplemented" |)
          M.pure Constant.None_))
      );
      (
        "__hash__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        `ForkCriteria` is hashable, so it can be stored in dictionaries.
        " in
          let _ := M.return_ (|
            M.call (|
              M.get_name (| globals, "hash" |),
              make_list [
                M.get_field (| M.get_name (| globals, "self" |), "_internal" |)
              ],
              make_dict []
            |)
          M.pure Constant.None_))
      )
    ].

Definition ByBlockNumber : Value.t :=
  builtins.make_klass
    [(globals, "ForkCriteria")]
    [

    ]
    [
      (
        "__init__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "block_number" ] |) in
          let _ := M.assign (|
            M.get_field (| M.get_name (| globals, "self" |), "_internal" |),
            make_tuple [ M.get_field (| M.get_name (| globals, "ForkCriteria" |), "BLOCK_NUMBER" |); M.get_name (| globals, "block_number" |) ]
          |) in
          let _ := M.assign (|
            M.get_field (| M.get_name (| globals, "self" |), "block_number" |),
            M.get_name (| globals, "block_number" |)
          |) in
          M.pure Constant.None_))
      );
      (
        "check",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "block_number"; "timestamp" ] |) in
          let _ := Constant.str "
        Check whether the block number has been reached.
        " in
          let _ := M.return_ (|
            Compare.gt_e (|
              M.get_name (| globals, "block_number" |),
              M.get_field (| M.get_name (| globals, "self" |), "block_number" |)
            |)
          M.pure Constant.None_))
      );
      (
        "__repr__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        String representation of this object.
        " in
          let _ := M.return_ (|
            (* At expr: unsupported node type: JoinedStr *)
          M.pure Constant.None_))
      )
    ].

Definition ByTimestamp : Value.t :=
  builtins.make_klass
    [(globals, "ForkCriteria")]
    [

    ]
    [
      (
        "__init__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "timestamp" ] |) in
          let _ := M.assign (|
            M.get_field (| M.get_name (| globals, "self" |), "_internal" |),
            make_tuple [ M.get_field (| M.get_name (| globals, "ForkCriteria" |), "TIMESTAMP" |); M.get_name (| globals, "timestamp" |) ]
          |) in
          let _ := M.assign (|
            M.get_field (| M.get_name (| globals, "self" |), "timestamp" |),
            M.get_name (| globals, "timestamp" |)
          |) in
          M.pure Constant.None_))
      );
      (
        "check",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "block_number"; "timestamp" ] |) in
          let _ := Constant.str "
        Check whether the timestamp has been reached.
        " in
          let _ := M.return_ (|
            Compare.gt_e (|
              M.get_name (| globals, "timestamp" |),
              M.get_field (| M.get_name (| globals, "self" |), "timestamp" |)
            |)
          M.pure Constant.None_))
      );
      (
        "__repr__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        String representation of this object.
        " in
          let _ := M.return_ (|
            (* At expr: unsupported node type: JoinedStr *)
          M.pure Constant.None_))
      )
    ].

Definition Unscheduled : Value.t :=
  builtins.make_klass
    [(globals, "ForkCriteria")]
    [

    ]
    [
      (
        "__init__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := M.assign (|
            M.get_field (| M.get_name (| globals, "self" |), "_internal" |),
            make_tuple [ M.get_field (| M.get_name (| globals, "ForkCriteria" |), "UNSCHEDULED" |); Constant.int 0 ]
          |) in
          M.pure Constant.None_))
      );
      (
        "check",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self"; "block_number"; "timestamp" ] |) in
          let _ := Constant.str "
        Unscheduled forks never occur.
        " in
          let _ := M.return_ (|
            Constant.bool false
          M.pure Constant.None_))
      );
      (
        "__repr__",
        fun (args kwargs : Value.t) => ltac:(M.monadic (
          let _ := M.set_locals (| args, kwargs, [ "self" ] |) in
          let _ := Constant.str "
        String representation of this object.
        " in
          let _ := M.return_ (|
            Constant.str "Unscheduled()"
          M.pure Constant.None_))
      )
    ].
