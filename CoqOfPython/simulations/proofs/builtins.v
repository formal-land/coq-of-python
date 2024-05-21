Require Import CoqOfPython.CoqOfPython.
Require Import simulations.proofs.CoqOfPython.
Require Import simulations.proofs.heap.

Require CoqOfPython.builtins.
Require ethereum.simulations.proofs.exceptions.

Import Run.

Module ArithmeticError.
  Definition to_value (exn : builtins.ArithmeticError.t) : Value.t :=
    match exn with
    | builtins.ArithmeticError.OverflowError =>
      Value.Make "builtins" "OverflowError" (Pointer.Imm Object.empty)
    end.
End ArithmeticError.

Module Exception.
  Definition to_value (exn : builtins.Exception.t) : Value.t :=
    match exn with
    | builtins.Exception.ArithmeticError exn => ArithmeticError.to_value exn
    | builtins.Exception.EthereumException exn => exceptions.EthereumException.to_value exn
    end.
End Exception.

(** Run of the primitive [len] function. *)
Definition run_len {A : Set} (stack : Stack.t) (heap : Heap.t)
  pointer object (l : list A) (to_value : A -> Value.t)
  (H_pointer : PointerRead.t stack heap pointer object)
  (H_object : object = Object.wrapper (Data.List (List.map to_value l))) :
  {{ stack, heap |
    builtins.len (make_list [Value.Make "builtins" "list" pointer]) (make_dict []) ⇓
    (fun (n : Z) => inl (Constant.int n))
  |
    fun stack' => stack' = stack,
    fun heap' => heap' = heap
  }}.
Proof.
  intros.
  cbn.
  apply Run.CallPrimitiveStateAllocImm.
  cbn.
  eapply run_read. {
    apply H_pointer.
  }
  rewrite H_object; cbn.
  now eapply Run.Pure; try rewrite List.map_length.
Defined.
