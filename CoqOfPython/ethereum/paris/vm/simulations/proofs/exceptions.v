Require Import CoqOfPython.CoqOfPython.
Require Import simulations.proofs.CoqOfPython.
Require Import simulations.proofs.heap.

Require Import ethereum.paris.vm.simulations.exceptions.

Import Run.

Module ExceptionalHalt.
  Definition to_value (exn : ExceptionalHalt.t) : Value.t :=
    match exn with
    | ExceptionalHalt.StackUnderflowError =>
      Value.Make "exceptions" "StackUnderflowError" (Pointer.Imm Object.empty)
    | ExceptionalHalt.StackOverflowError =>
      Value.Make "exceptions" "StackOverflowError" (Pointer.Imm Object.empty)
    | ExceptionalHalt.OutOfGasError =>
      Value.Make "exceptions" "OutOfGasError" (Pointer.Imm Object.empty)
    | ExceptionalHalt.InvalidOpcode code =>
      Value.Make "exceptions" "InvalidOpcode" (Pointer.Imm (Object.wrapper (Data.Integer code)))
    | ExceptionalHalt.InvalidJumpDestError =>
      Value.Make "exceptions" "InvalidJumpDestError" (Pointer.Imm Object.empty)
    | ExceptionalHalt.StackDepthLimitError =>
      Value.Make "exceptions" "StackDepthLimitError" (Pointer.Imm Object.empty)
    | ExceptionalHalt.WriteInStaticContext =>
      Value.Make "exceptions" "WriteInStaticContext" (Pointer.Imm Object.empty)
    | ExceptionalHalt.OutOfBoundsRead =>
      Value.Make "exceptions" "OutOfBoundsRead" (Pointer.Imm Object.empty)
    | ExceptionalHalt.InvalidParameter =>
      Value.Make "exceptions" "InvalidParameter" (Pointer.Imm Object.empty)
    | ExceptionalHalt.InvalidContractPrefix =>
      Value.Make "exceptions" "InvalidContractPrefix" (Pointer.Imm Object.empty)
    | ExceptionalHalt.AddressCollision =>
      Value.Make "exceptions" "AddressCollision" (Pointer.Imm Object.empty)
    end.
End ExceptionalHalt.
