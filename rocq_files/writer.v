Require Import String.

Inductive writer (A : Type) : Type := Writer : A -> string -> writer A.

Check Writer.

Arguments Writer {A} _ _.

Definition writer_ret {A : Type} (x : A) : writer A := Writer x EmptyString.

Fixpoint concat (x y : string) : string :=
  match x with
    | EmptyString => y
    | String x xs => String x (concat xs y)
  end.

Fixpoint writer_bind {A B : Type} (w : writer A) (f : A -> writer B) : writer B :=
  match w with
    | Writer a s1 => match f a with
      | Writer b s2 => Writer b (concat s1 s2)
    end
  end.

Lemma writer_monad_left_id :
  forall (A B : Type) (a : A) (f : A -> writer B),
    writer_bind (writer_ret a) f = f a.
Proof. intros A B a f. simpl. destruct (f a). reflexivity. Qed.

Lemma concat_assoc :
  forall (a b c : string), concat a (concat b c) = concat (concat a b) c.
Proof. intros a b c. induction a as [| x xs IH]. 
  simpl. reflexivity. 
  cbn. rewrite -> IH. reflexivity.
Qed.

Lemma concat_with_empty :
  forall (s : string), concat s "" = s.
Proof. intros s; induction s as [| x xs IH].
  simpl. reflexivity.
  simpl. rewrite -> IH. reflexivity.
Qed.

Lemma writer_monad_right_id :
  forall (A : Type) (w : writer A),
    writer_bind w (@writer_ret A) = w.
Proof.
  intros A w. destruct w. simpl. rewrite concat_with_empty. reflexivity.
Qed.

Lemma writer_monad_assoc :
  forall (A B C : Type) (w : writer A)
         (f : A -> writer B) (g : B -> writer C),
    writer_bind (writer_bind w f) g = writer_bind w (fun x => writer_bind (f x) g).
Proof.
  intros A B C w f g.
  destruct w as [a s].
  simpl.
  destruct (f a) as [b s'].
  simpl.
  destruct (g b) as [c s''].
  simpl.
  rewrite concat_assoc.
  reflexivity.
Qed.

Theorem writer_is_monad :
  (forall (A B : Type) (a : A) (f : A -> writer B),
      writer_bind (writer_ret a) f = f a)
  /\ (forall (A : Type) (m : writer A),
         writer_bind m (@writer_ret A) = m)
  /\ (forall (A B C : Type) (m : writer A) (f : A -> writer B) (g : B -> writer C),
         writer_bind (writer_bind m f) g = writer_bind m (fun x => writer_bind (f x) g)).
Proof.
  split; [| split].
  - exact (@writer_monad_left_id).
  - exact (@writer_monad_right_id).
  - exact (@writer_monad_assoc).
Qed.

Require Extraction.
Extraction Language Haskell.
Extraction "writer.hs" writer writer_ret writer_bind.