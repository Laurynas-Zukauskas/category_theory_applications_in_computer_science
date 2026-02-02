Require Import ExtLib.Structures.Monads.

Set Implicit Arguments.
Set Strict Implicit.

Inductive state (S : Type) (T : Type) : Type := mkState : (S -> T * S) -> state S T.

Check state.
Check fun s => (0, s).

Definition test (n m : nat) := n + m.

Check test 0 1.

Definition double {A B : Type} (a : A) (b : B) := (a, b).

Definition ret := fun {S : Type} {T : Type} (v : T) => mkState ((double v) : S -> T * S).

Definition bind_helper {S : Type} {A : Type} {B : Type} (s : state S A) (g : A -> state S B) (s0 : S) :=
  match s with
    | mkState f => match f s0 with
      | (a, s1) => match g a with
        | mkState h => h s1
      end
    end
  end.

Definition bind := fun {S : Type} {T : Type} (c1 : state S T) (c2 : T -> state S T) =>
  mkState (bind_helper c1 c2).
  
Require Extraction.
Extraction Language Haskell.
Set Extraction Optimize.
Set Extraction KeepSingleton.
Extraction "state.hs" state ret bind.