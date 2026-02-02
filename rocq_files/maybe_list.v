Inductive maybe (A : Type) : Type :=
  | Nothing : maybe A
  | Just : A -> maybe A.

Arguments Nothing {A}.
Arguments Just {A} _.

Fixpoint maybe_map {A B : Type} (f : A -> B) (m : maybe A) : maybe B :=
  match m with
  | Nothing => Nothing
  | Just a => Just (f a)
  end.

Lemma maybe_map_id : forall (A : Type) (m : maybe A),
    maybe_map (fun x => x) m = m.
Proof.
  intros A m. induction m; reflexivity.
Qed.

Lemma maybe_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (m : maybe A),
    maybe_map (fun x => g (f x)) m = maybe_map g (maybe_map f m).
Proof.
  intros A B C f g m. induction m; reflexivity.
Qed.

Definition maybe_ret {A : Type} (x : A) : maybe A := Just x.

Fixpoint maybe_bind {A B : Type} (m : maybe A) (f : A -> maybe B) :=
  match m with
  | Nothing => Nothing
  | Just a => f a
  end.

Lemma maybe_monad_left_id :
  forall (A B : Type) (a : A) (f : A -> maybe B),
    maybe_bind (maybe_ret a) f = f a.
Proof. reflexivity. Qed.

Lemma maybe_monad_right_id :
  forall (A : Type) (m : maybe A),
    maybe_bind m (@maybe_ret A) = m.
Proof.
  intros A m; induction m; reflexivity.
Qed.

Lemma maybe_monad_assoc :
  forall (A B C : Type) (m : maybe A)
         (f : A -> maybe B) (g : B -> maybe C),
  maybe_bind (maybe_bind m f) g = 
  maybe_bind m (fun x => maybe_bind (f x) g).
Proof.
  intros A B C m f g. induction m; reflexivity.
Qed.

Theorem maybe_is_monad :
  (forall (A B : Type) (a : A) (f : A -> maybe B),
      maybe_bind (maybe_ret a) f = f a)
  /\ (forall (A : Type) (m : maybe A),
         maybe_bind m (@maybe_ret A) = m)
  /\ (forall (A B C : Type) (m : maybe A) (f : A -> maybe B) (g : B -> maybe C),
         maybe_bind (maybe_bind m f) g = maybe_bind m (fun x => maybe_bind (f x) g)).
Proof.
  split; [| split].
  - exact (@maybe_monad_left_id).
  - exact (@maybe_monad_right_id).
  - exact (@maybe_monad_assoc).
Qed.

Inductive list (A : Type) : Type :=
  | Nil : list A
  | Cons : A -> list A -> list A.
  
Arguments Nil {A}.
Arguments Cons {A} _ _.

Fixpoint map {A B : Type} (f : A -> B) (m : list A) : list B :=
  match m with
  | Nil => Nil
  | Cons x xs => Cons (f x) (map f xs)
  end.

Lemma list_map_id : forall (A : Type) (m : list A),
    map (fun x => x) m = m.
Proof.
  intros A m. induction m as [| x xs IH]. 
    reflexivity.
    simpl. rewrite -> IH. reflexivity.
Qed.

Lemma list_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (m : list A),
    map (fun x => g (f x)) m = map g (map f m).
Proof.
  intros A B C f g m. induction m as [| x xs IH]. 
    reflexivity.
    simpl. rewrite -> IH. reflexivity.
Qed.

Fixpoint maybe_head {A : Type} (l : list A) : maybe A :=
  match l with
  | Nil => Nothing
  | Cons x _ => Just x
  end.

Lemma natural_head :
  forall (A B : Type) (f : A -> B) (l : list A), maybe_head (map f l) = maybe_map f (maybe_head l).
Proof. intros A B f l. induction l; simpl; reflexivity.

Require Extraction.
Extraction Language Haskell.
Extraction "maybe_list.hs" maybe maybe_map maybe_ret maybe_bind list map maybe_head.