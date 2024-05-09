Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

Inductive Any : Set :=.
Inductive Callable : Set :=.
Inductive ClassVar : Set :=.
Inductive Optional : Set :=.
Inductive Protocol : Set :=.
Inductive Tuple : Set :=.
Inductive Type_ : Set :=.
Inductive TypeVar : Set :=.
Parameter runtime_checkable : Value.t.
