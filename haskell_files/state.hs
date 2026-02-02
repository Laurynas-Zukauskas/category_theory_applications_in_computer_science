module State where

import qualified Prelude

data Prod a b =
   Pair a b

data State s t =
   MkState (s -> Prod t s)

double :: a1 -> a2 -> Prod a1 a2
double a b =
  Pair a b

ret :: a2 -> State a1 a2
ret v =
  MkState (double v)

bind_helper :: (State a1 a2) -> (a2 -> State a1 a3) -> a1 -> Prod a3 a1
bind_helper s g s0 =
  case s of {
   MkState f -> case f s0 of {
                 Pair a s1 -> case g a of {
                               MkState h -> h s1}}}

bind :: (State a1 a2) -> (a2 -> State a1 a2) -> State a1 a2
bind c1 c2 =
  MkState (bind_helper c1 c2)

