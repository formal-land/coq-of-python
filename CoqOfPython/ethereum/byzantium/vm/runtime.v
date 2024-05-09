Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Runtime Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Runtime related operations used while executing EVM code.
".

Require typing.
Axiom typing_Set_ :
  IsGlobalAlias globals typing.globals "Set_".

Require ethereum.base_types.
Axiom ethereum_base_types_Uint :
  IsGlobalAlias globals ethereum.base_types.globals "Uint".

Require instructions.
Axiom instructions_Ops :
  IsGlobalAlias globals instructions.globals "Ops".

Definition get_valid_jump_destinations : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "code" ] |) in
    let _ := Constant.str "
    Analyze the evm code to obtain the set of valid jump destinations.

    Valid jump destinations are defined as follows:
        * The jump destination is less than the length of the code.
        * The jump destination should have the `JUMPDEST` opcode (0x5B).
        * The jump destination shouldn't be part of the data corresponding to
          `PUSH-N` opcodes.

    Note - Jump destinations are 0-indexed.

    Parameters
    ----------
    code :
        The EVM code which is to be executed.

    Returns
    -------
    valid_jump_destinations: `Set[Uint]`
        The set of valid jump destinations in the code.
    " in
    let valid_jump_destinations :=
      M.call (|
        M.get_name (| globals, "set" |),
        make_list [],
        make_dict []
      |) in
    let pc :=
      M.call (|
        M.get_name (| globals, "Uint" |),
        make_list [
          Constant.int 0
        ],
        make_dict []
      |) in
    While Compare.lt (| M.get_name (| globals, "pc" |), M.call (|
    M.get_name (| globals, "len" |),
    make_list [
      M.get_name (| globals, "code" |)
    ],
    make_dict []
  |) |) do
(* At stmt: unsupported node type: Try *)
      let _ :=
        (* if *)
        M.if_then_else (|
          Compare.eq (| M.get_name (| globals, "current_opcode" |), M.get_field (| M.get_name (| globals, "Ops" |), "JUMPDEST" |) |),
        (* then *)
        ltac:(M.monadic (
          let _ := M.call (|
    M.get_field (| M.get_name (| globals, "valid_jump_destinations" |), "add" |),
    make_list [
      M.get_name (| globals, "pc" |)
    ],
    make_dict []
  |) in
          M.pure Constant.None_
        (* else *)
        )), ltac:(M.monadic (
          let _ :=
            (* if *)
            M.if_then_else (|
              (* At expr: unsupported node type: Compare *),
            (* then *)
            ltac:(M.monadic (
              let push_data_size :=
                BinOp.add (|
                  BinOp.sub (|
                    M.get_field (| M.get_name (| globals, "current_opcode" |), "value" |),
                    M.get_field (| M.get_field (| M.get_name (| globals, "Ops" |), "PUSH1" |), "value" |)
                  |),
                  Constant.int 1
                |) in
              let pc := BinOp.add
                M.get_name (| globals, "push_data_size" |)
                M.get_name (| globals, "push_data_size" |) in
              M.pure Constant.None_
            (* else *)
            )), ltac:(M.monadic (
              M.pure Constant.None_
            )) |) in
          M.pure Constant.None_
        )) |) in
      let pc := BinOp.add
        Constant.int 1
        Constant.int 1 in
    EndWhile.
    let _ := M.return_ (|
      M.get_name (| globals, "valid_jump_destinations" |)
    |) in
    M.pure Constant.None_)).
