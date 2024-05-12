Require Import CoqOfPython.CoqOfPython.

Module ExceptionalHalt.
  Inductive t : Set :=
  | StackUnderflowError
  | StackOverflowError
  | OutOfGasError
  | InvalidOpcode (code : Z)
  | InvalidJumpDestError
  | StackDepthLimitError
  | WriteInStaticContext
  | OutOfBoundsRead
  | InvalidParameter
  | InvalidContractPrefix
  | AddressCollision.
End ExceptionalHalt.

Module Revert.
  Inductive t : Set :=.
End Revert.
