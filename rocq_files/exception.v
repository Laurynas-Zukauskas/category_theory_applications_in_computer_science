Require Import String.

Inductive exception (A : Type) : Type :=
  | Good : A -> exception A
  | Bad : string -> exception A.
  
Arguments Good {A} _.
Arguments Bad {A} _.

Fixpoint exception_map {A B : Type} (f : A -> B) (e : exception A) : exception B :=
  match e with
  | Bad ex => Bad ex
  | Good a => Good (f a)
  end.

(* Functor laws *)

Lemma exception_map_id : forall (A : Type) (e : exception A),
    exception_map (fun x => x) e = e.
Proof.
  intros A m. induction m; reflexivity.
Qed.

Lemma exception_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (e : exception A),
    exception_map (fun x => g (f x)) e = exception_map g (exception_map f e).
Proof.
  intros A B C f g e. induction e; reflexivity.
Qed.

Definition exception_ret {A : Type} (x : A) : exception A := Good x.

Fixpoint exception_bind {A B : Type} (e : exception A) (f : A -> exception B) : exception B :=
  match e with
  | Bad ex => Bad ex
  | Good a => f a
  end.

Lemma exception_monad_left_id :
  forall (A B : Type) (a : A) (f : A -> exception B),
    exception_bind (exception_ret a) f = f a.
Proof. reflexivity. Qed.

Lemma exception_monad_right_id :
  forall (A : Type) (e : exception A),
    exception_bind e (@exception_ret A) = e.
Proof.
  intros A e; induction e; reflexivity.
Qed.

Lemma exception_monad_assoc :
  forall (A B C : Type) (e : exception A)
         (f : A -> exception B) (g : B -> exception C),
    exception_bind (exception_bind e f) g = exception_bind e (fun x => exception_bind (f x) g).
Proof.
  intros A B C e f g. induction e; reflexivity.
Qed.

Theorem exception_is_monad :
  (forall (A B : Type) (a : A) (f : A -> exception B),
      exception_bind (exception_ret a) f = f a)
  /\ (forall (A : Type) (m : exception A),
         exception_bind m (@exception_ret A) = m)
  /\ (forall (A B C : Type) (m : exception A) (f : A -> exception B) (g : B -> exception C),
         exception_bind (exception_bind m f) g = exception_bind m (fun x => exception_bind (f x) g)).
Proof.
  split; [| split].
  - exact (@exception_monad_left_id).
  - exact (@exception_monad_right_id).
  - exact (@exception_monad_assoc).
Qed.

Require Extraction.
Extraction Language Haskell.
Extraction "exception.hs" exception exception_map exception_ret exception_bind.