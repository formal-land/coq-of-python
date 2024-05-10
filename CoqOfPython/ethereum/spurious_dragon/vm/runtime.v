Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.spurious_dragon.vm.runtime".

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

Axiom typing_imports :
  AreImported globals "typing" [ "Set" ].

Axiom ethereum_base_types_imports :
  AreImported globals "ethereum.base_types" [ "Uint" ].

Axiom ethereum_spurious_dragon_vm_instructions_imports :
  AreImported globals "ethereum.spurious_dragon.vm.instructions" [ "Ops" ].

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
    let _ :=
      M.while (|
        Compare.lt (|
      M.get_name (| globals, "pc" |),
      M.call (|
        M.get_name (| globals, "len" |),
        make_list [
          M.get_name (| globals, "code" |)
        ],
        make_dict []
      |)
    |),
        ltac:(M.monadic (
(* At stmt: unsupported node type: Try *)
          let _ :=
            (* if *)
            M.if_then_else (|
              Compare.eq (|
                M.get_name (| globals, "current_opcode" |),
                M.get_field (| M.get_name (| globals, "Ops" |), "JUMPDEST" |)
              |),
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
                  BoolOp.and (|
                    Compare.lt_e (|
                      M.get_field (| M.get_field (| M.get_name (| globals, "Ops" |), "PUSH1" |), "value" |),
                      M.get_field (| M.get_name (| globals, "current_opcode" |), "value" |)
                    |),
                    ltac:(M.monadic (
                      Compare.lt_e (|
                        M.get_field (| M.get_name (| globals, "current_opcode" |), "value" |),
                        M.get_field (| M.get_field (| M.get_name (| globals, "Ops" |), "PUSH32" |), "value" |)
                      |)
                    ))
                  |),
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
          M.pure Constant.None_
        )),
        ltac:(M.monadic (
          M.pure Constant.None_
        ))
    |) in
    let _ := M.return_ (|
      M.get_name (| globals, "valid_jump_destinations" |)
    |) in
    M.pure Constant.None_)).
