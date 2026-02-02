From Coq Require Import List.
Import ListNotations.
From Coq Require Import Program.Basics.
From Coq Require Import Init.Nat.
From Coq Require Import Logic.FunctionalExtensionality.
Set Implicit Arguments.

Inductive btree (A : Type) : Type :=
| Leaf : A -> btree A
| Node : btree A -> btree A -> btree A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint tree_map {A B : Type} (f : A -> B) (t : btree A) : btree B :=
  match t with
  | Leaf x => Leaf (f x)
  | Node l r => Node (tree_map f l) (tree_map f r)
  end.

Lemma tree_map_id : forall (A : Type) (t : btree A),
    tree_map (fun x => x) t = t.
Proof.
  intros A t. induction t as [x | l IHl r IHr].
    - simpl. reflexivity.
    - simpl. rewrite IHl, IHr. reflexivity.
Qed.

Lemma tree_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (t : btree A),
    tree_map (fun x => g (f x)) t = tree_map g (tree_map f t).
Proof.
  intros A B C f g t. induction t as [x | l IHl r IHr].
    - simpl. reflexivity.
    - simpl. rewrite IHl, IHr. reflexivity.
Qed.

Definition tree_ret {A : Type} (x : A) : btree A := Leaf x.

Fixpoint tree_bind {A B : Type} (t : btree A) (f : A -> btree B) : btree B :=
  match t with
  | Leaf x => f x
  | Node l r => Node (tree_bind l f) (tree_bind r f)
  end.

Lemma tree_monad_left_id :
  forall (A B : Type) (a : A) (f : A -> btree B),
    tree_bind (tree_ret a) f = f a.
Proof. intros; simpl; reflexivity. Qed.

Lemma tree_monad_right_id :
  forall (A : Type) (m : btree A),
    tree_bind m (@tree_ret A) = m.
Proof.
  intros A m; induction m as [x | l IHl r IHr].
  - simpl. reflexivity.
  - simpl. rewrite IHl, IHr. reflexivity.
Qed.

Lemma tree_monad_assoc :
  forall (A B C : Type) (m : btree A)
         (f : A -> btree B) (g : B -> btree C),
    tree_bind (tree_bind m f) g = tree_bind m (fun x => tree_bind (f x) g).
Proof.
  intros A B C m f g. induction m as [x | l IHl r IHr].
  - simpl. reflexivity.
  - simpl. rewrite IHl, IHr. reflexivity.
Qed.

Lemma tree_map_via_bind :
  forall (A B : Type) (f : A -> B) (t : btree A),
    tree_map f t = tree_bind t (fun x => Leaf (f x)).
Proof.
  intros A B f t. induction t as [x | l IHl r IHr].
  - simpl. reflexivity.
  - simpl. rewrite IHl, IHr. reflexivity.
Qed.

Theorem tree_is_monad :
  (forall (A B : Type) (a : A) (f : A -> btree B),
      tree_bind (tree_ret a) f = f a)
  /\ (forall (A : Type) (m : btree A),
         tree_bind m (@tree_ret A) = m)
  /\ (forall (A B C : Type) (m : btree A) (f : A -> btree B) (g : B -> btree C),
         tree_bind (tree_bind m f) g = tree_bind m (fun x => tree_bind (f x) g)).
Proof.
  split; [| split].
  - exact (@tree_monad_left_id).
  - exact (@tree_monad_right_id).
  - exact (@tree_monad_assoc).
Qed.

Require Extraction.
Extraction Language Haskell.
Extraction "btree.hs" btree tree_map tree_ret tree_bind.