Require Import CoqOfPython.CoqOfPython.

Definition globals : string := "ethereum.london.vm.precompiled_contracts.blake2f".

Definition expr_1 : Value.t :=
  Constant.str "
Ethereum Virtual Machine (EVM) Blake2 PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the `Blake2` precompiled contract.
".

Axiom ethereum_crypto_blake2_imports :
  AreImported globals "ethereum.crypto.blake2" [ "Blake2b" ].

Axiom ethereum_utils_ensure_imports :
  AreImported globals "ethereum.utils.ensure" [ "ensure" ].

Axiom ethereum_london_vm_imports :
  AreImported globals "ethereum.london.vm" [ "Evm" ].

Axiom ethereum_london_vm_gas_imports :
  AreImported globals "ethereum.london.vm.gas" [ "GAS_BLAKE2_PER_ROUND"; "charge_gas" ].

Axiom ethereum_london_vm_exceptions_imports :
  AreImported globals "ethereum.london.vm.exceptions" [ "InvalidParameter" ].

Definition blake2f : Value.t -> Value.t -> M :=
  fun (args kwargs : Value.t) => ltac:(M.monadic (
    let _ := M.set_locals (| args, kwargs, [ "evm" ] |) in
    let _ := Constant.str "
    Writes the Blake2 hash to output.

    Parameters
    ----------
    evm :
        The current EVM frame.
    " in
    let data :=
      M.get_field (| M.get_field (| M.get_name (| globals, "evm" |), "message" |), "data" |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.eq (|
        M.call (|
          M.get_name (| globals, "len" |),
          make_list [
            M.get_name (| globals, "data" |)
          ],
          make_dict []
        |),
        Constant.int 213
      |);
      M.get_name (| globals, "InvalidParameter" |)
    ],
    make_dict []
  |) in
    let blake2b :=
      M.call (|
        M.get_name (| globals, "Blake2b" |),
        make_list [],
        make_dict []
      |) in
    let _ := M.assign (|
      make_tuple [ M.get_name (| globals, "rounds" |); M.get_name (| globals, "h" |); M.get_name (| globals, "m" |); M.get_name (| globals, "t_0" |); M.get_name (| globals, "t_1" |); M.get_name (| globals, "f" |) ],
      M.call (|
        M.get_field (| M.get_name (| globals, "blake2b" |), "get_blake2_parameters" |),
        make_list [
          M.get_name (| globals, "data" |)
        ],
        make_dict []
      |)
    |) in
    let _ := M.call (|
    M.get_name (| globals, "charge_gas" |),
    make_list [
      M.get_name (| globals, "evm" |);
      BinOp.mult (|
        M.get_name (| globals, "GAS_BLAKE2_PER_ROUND" |),
        M.get_name (| globals, "rounds" |)
      |)
    ],
    make_dict []
  |) in
    let _ := M.call (|
    M.get_name (| globals, "ensure" |),
    make_list [
      Compare.in_ (|
        M.get_name (| globals, "f" |),
        make_list [
          Constant.int 0;
          Constant.int 1
        ]
      |);
      M.get_name (| globals, "InvalidParameter" |)
    ],
    make_dict []
  |) in
    let _ := M.assign (|
      M.get_field (| M.get_name (| globals, "evm" |), "output" |),
      M.call (|
        M.get_field (| M.get_name (| globals, "blake2b" |), "compress" |),
        make_list [
          M.get_name (| globals, "rounds" |);
          M.get_name (| globals, "h" |);
          M.get_name (| globals, "m" |);
          M.get_name (| globals, "t_0" |);
          M.get_name (| globals, "t_1" |);
          M.get_name (| globals, "f" |)
        ],
        make_dict []
      |)
    |) in
    M.pure Constant.None_)).
