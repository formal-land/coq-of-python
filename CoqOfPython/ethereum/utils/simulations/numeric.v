Require Import CoqOfPython.CoqOfPython.
Require Import simulations.CoqOfPython.
Require Import simulations.builtins.

Require ethereum.simulations.base_types.
Module U256 := base_types.U256.
Module Uint := base_types.Uint.

Import simulations.CoqOfPython.Notations.

(* def ceil32(value: Uint) -> Uint:
    """
    Converts a unsigned integer to the next closest multiple of 32.

    Parameters
    ----------
    value :
        The value whose ceil32 is to be calculated.

    Returns
    -------
    ceil32 : `ethereum.base_types.U256`
        The same value if it's a perfect multiple of 32
        else it returns the smallest multiple of 32
        that is greater than `value`.
    """
    ceiling = Uint(32)
    remainder = value % ceiling
    if remainder == Uint(0):
        return value
    else:
        return value + ceiling - remainder *)

(* TODO: Finish below *)
Definition ceil32 (value : Uint.t) : Uint.t. Admitted.
 (* :=
  let ceiling := Uint.Make 32 in
  let remainder := value % ceiling in
  if remainder =? Uint 0
  then value
  else value + ceiling - remainder. *)
