Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.fork_criteria".

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

Axiom abc_imports_ABC :
  IsImported globals "abc" "ABC".
Axiom abc_imports_abstractmethod :
  IsImported globals "abc" "abstractmethod".

Axiom typing_imports_Final :
  IsImported globals "typing" "Final".
Axiom typing_imports_Tuple :
  IsImported globals "typing" "Tuple".

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
            (* if *)
            M.if_then_else (|
              M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "other" |);
                  M.get_name (| globals, "ForkCriteria" |)
                ],
                make_dict []
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                Compare.eq (|
                  M.get_field (| M.get_name (| globals, "self" |), "_internal" |),
                  M.get_field (| M.get_name (| globals, "other" |), "_internal" |)
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.get_name (| globals, "NotImplemented" |)
          |) in
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
            (* if *)
            M.if_then_else (|
              M.call (|
                M.get_name (| globals, "isinstance" |),
                make_list [
                  M.get_name (| globals, "other" |);
                  M.get_name (| globals, "ForkCriteria" |)
                ],
                make_dict []
              |),
            (* then *)
            ltac:(M.monadic (
              let _ := M.return_ (|
                Compare.lt (|
                  M.get_field (| M.get_name (| globals, "self" |), "_internal" |),
                  M.get_field (| M.get_name (| globals, "other" |), "_internal" |)
                |)
              |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          let _ := M.return_ (|
            M.get_name (| globals, "NotImplemented" |)
          |) in
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
          |) in
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
          |) in
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
            Constant.str "(* At expr: unsupported node type: JoinedStr *)"
          |) in
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
          |) in
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
            Constant.str "(* At expr: unsupported node type: JoinedStr *)"
          |) in
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
          |) in
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
          |) in
          M.pure Constant.None_))
      )
    ].
