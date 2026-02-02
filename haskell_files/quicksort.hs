module Quicksort where

import qualified Prelude

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

isZero :: Nat -> Bool
isZero n =
  case n of {
   O -> True;
   S _ -> False}

data List =
   Nil
 | Cons Nat List

concat :: List -> List -> List
concat l r =
  case l of {
   Nil -> r;
   Cons l0 ls -> Cons l0 (concat ls r)}

less :: Nat -> Nat -> Bool
less n m =
  case m of {
   O -> False;
   S q -> case n of {
           O -> True;
           S p -> less p q}}

lesseq :: Nat -> Nat -> Bool
lesseq n m =
  case n of {
   O -> True;
   S p -> case m of {
           O -> False;
           S q -> lesseq p q}}

greatereq :: Nat -> Nat -> Bool
greatereq n m =
  case m of {
   O -> True;
   S q -> case n of {
           O -> False;
           S p -> greatereq p q}}

allless :: List -> Nat -> List
allless l n =
  case l of {
   Nil -> Nil;
   Cons m ls ->
    case less m n of {
     True -> Cons m (allless ls n);
     False -> allless ls n}}

allgeq :: List -> Nat -> List
allgeq l n =
  case l of {
   Nil -> Nil;
   Cons m ls ->
    case greatereq m n of {
     True -> Cons m (allgeq ls n);
     False -> allgeq ls n}}

qaux :: Nat -> List -> List
qaux n l =
  case n of {
   O -> Nil;
   S p ->
    case l of {
     Nil -> Nil;
     Cons m ls ->
      concat (qaux p (allless ls m)) (Cons m (qaux p (allgeq ls m)))}}

length :: List -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ ls -> S (length ls)}

quicksort :: List -> List
quicksort l =
  qaux (length l) l

