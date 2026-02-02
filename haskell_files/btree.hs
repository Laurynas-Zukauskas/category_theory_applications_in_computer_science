module Btree where

import qualified Prelude

data Btree a =
   Leaf a
 | Node (Btree a) (Btree a)

tree_map :: (a1 -> a2) -> (Btree a1) -> Btree a2
tree_map f t =
  case t of {
   Leaf x -> Leaf (f x);
   Node l r -> Node (tree_map f l) (tree_map f r)}

tree_ret :: a1 -> Btree a1
tree_ret x =
  Leaf x

tree_bind :: (Btree a1) -> (a1 -> Btree a2) -> Btree a2
tree_bind t f =
  case t of {
   Leaf x -> f x;
   Node l r -> Node (tree_bind l f) (tree_bind r f)}

