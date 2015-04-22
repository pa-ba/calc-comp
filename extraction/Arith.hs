module Arith where

import qualified Prelude

data Expr =
   Val Prelude.Int
 | Add Expr Expr

data Code =
   PUSH Prelude.Int Code
 | ADD Code
 | HALT

comp' :: Expr -> Code -> Code
comp' e c =
  case e of {
   Val n -> PUSH n c;
   Add x y -> comp' x (comp' y (ADD c))}

comp :: Expr -> Code
comp e =
  comp' e HALT

