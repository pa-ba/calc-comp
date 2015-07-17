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
comp' x c =
  case x of {
   Val n -> PUSH n c;
   Add x1 x2 -> comp' x1 (comp' x2 (ADD c))}

comp :: Expr -> Code
comp x =
  comp' x HALT

