Inductive nat : Type :=
   | O : nat
   | S : nat -> nat.

Definition isZero (n:nat) : bool :=
  match n with
   O => true
   |S p => false
  end.

Inductive List: Set :=
 | nil: List
 | cons: nat -> List -> List.

Fixpoint Concat (L R: List) : List :=
 match L with
 | nil => R
 | cons l ls => cons l (Concat ls R)
end.  

Fixpoint Less (n m:nat) :=
  match m with
   O => false
  |S q => match n with
          O => true
         |S p => Less p q
         end
  end.      

Fixpoint Lesseq (n m:nat) :=
  match n with
   O => true
  |S p => match m with
           O => false
          |S q => Lesseq p q
          end
  end.

Fixpoint Greatereq (n m:nat) :=
  match m with
   O => true
  |S q => match n with
           O => false
          |S p => Greatereq p q
          end
  end.


Fixpoint Allless (l:List) (n:nat) : List :=
  match l with
   nil => nil
  |cons m ls => match Less m n with
                 false => Allless ls n
                |true => cons m (Allless ls n)
                end
end.               

Fixpoint Allgeq (l:List) (n:nat) : List :=
  match l with
   nil => nil
  |cons m ls => match Greatereq m n with
                 false => Allgeq ls n
                |true => cons m (Allgeq ls n)
                end
end.  

Fixpoint qaux (n:nat) (l:List) : List := 
  match n with
  O => nil
 |S p => match l with
         nil => nil
        |cons m ls => Concat (qaux p (Allless ls m)) (cons m (qaux p (Allgeq ls m)))
        end
 end.

Fixpoint length (l:List) : nat :=
 match l with
  nil => O
|cons m ls => S (length ls)
end.

Fixpoint Quicksort (l:List) : List := qaux (length l) l.

Require Extraction.
Extraction Language Haskell.
Extraction "quicksort.hs" nat isZero List Concat Less Lesseq Greatereq Allless Allgeq qaux length Quicksort.