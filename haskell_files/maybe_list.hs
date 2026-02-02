module Maybe_list where

import qualified Prelude

data Maybe a =
   Nothing
 | Just a

maybe_map :: (a1 -> a2) -> (Maybe a1) -> Maybe a2
maybe_map f m =
  case m of {
   Nothing -> Nothing;
   Just a -> Just (f a)}

maybe_ret :: a1 -> Maybe a1
maybe_ret x =
  Just x

maybe_bind :: (Maybe a1) -> (a1 -> Maybe a2) -> Maybe a2
maybe_bind m f =
  case m of {
   Nothing -> Nothing;
   Just a -> f a}

data List a =
   Nil
 | Cons a (List a)

map :: (a1 -> a2) -> (List a1) -> List a2
map f m =
  case m of {
   Nil -> Nil;
   Cons x xs -> Cons (f x) (map f xs)}

maybe_head :: (List a1) -> Maybe a1
maybe_head l =
  case l of {
   Nil -> Nothing;
   Cons x _ -> Just x}

