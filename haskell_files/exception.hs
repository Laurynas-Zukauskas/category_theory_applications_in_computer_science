module Exception where

import qualified Prelude

data Bool =
   True
 | False

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

data String =
   EmptyString
 | String0 Ascii0 String

data Exception a =
   Good a
 | Bad String

exception_map :: (a1 -> a2) -> (Exception a1) -> Exception a2
exception_map f e =
  case e of {
   Good a -> Good (f a);
   Bad ex -> Bad ex}

exception_ret :: a1 -> Exception a1
exception_ret x =
  Good x

exception_bind :: (Exception a1) -> (a1 -> Exception a2) -> Exception a2
exception_bind e f =
  case e of {
   Good a -> f a;
   Bad ex -> Bad ex}

