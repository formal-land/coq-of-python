Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

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

Require ethereum.crypto.blake2.
Axiom ethereum_crypto_blake2_Blake2b :
  IsGlobalAlias globals ethereum.crypto.blake2.globals "Blake2b".

Require ethereum.utils.ensure.
Axiom ethereum_utils_ensure_ensure :
  IsGlobalAlias globals ethereum.utils.ensure.globals "ensure".

Require ethereum.muir_glacier.vm.__init__.
Axiom ethereum_muir_glacier_vm___init___Evm :
  IsGlobalAlias globals ethereum.muir_glacier.vm.__init__.globals "Evm".

Require ethereum.muir_glacier.vm.gas.
Axiom ethereum_muir_glacier_vm_gas_GAS_BLAKE2_PER_ROUND :
  IsGlobalAlias globals ethereum.muir_glacier.vm.gas.globals "GAS_BLAKE2_PER_ROUND".
Axiom ethereum_muir_glacier_vm_gas_charge_gas :
  IsGlobalAlias globals ethereum.muir_glacier.vm.gas.globals "charge_gas".

Require ethereum.muir_glacier.vm.exceptions.
Axiom ethereum_muir_glacier_vm_exceptions_InvalidParameter :
  IsGlobalAlias globals ethereum.muir_glacier.vm.exceptions.globals "InvalidParameter".

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
      Compare.in (|
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
