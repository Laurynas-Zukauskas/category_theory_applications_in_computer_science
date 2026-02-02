module Writer where

import qualified Prelude

data Bool =
   True
 | False

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

data String =
   EmptyString
 | String0 Ascii0 String

data Writer0 a =
   Writer a String

writer_ret :: a1 -> Writer0 a1
writer_ret x =
  Writer x EmptyString

concat :: String -> String -> String
concat x y =
  case x of {
   EmptyString -> y;
   String0 x0 xs -> String0 x0 (concat xs y)}

writer_bind :: (Writer0 a1) -> (a1 -> Writer0 a2) -> Writer0 a2
writer_bind w f =
  case w of {
   Writer a s1 -> case f a of {
                   Writer b s2 -> Writer b (concat s1 s2)}}

