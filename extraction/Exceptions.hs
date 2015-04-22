module Exceptions where

import qualified Prelude

data Expr =
   Val Prelude.Int
 | Add Expr Expr
 | Throw
 | Catch Expr Expr

data Code =
   PUSH Prelude.Int Code
 | ADD Code
 | FAIL
 | UNMARK Code
 | MARK Code Code
 | HALT

comp' :: Expr -> Code -> Code
comp' e c =
  case e of {
   Val n -> PUSH n c;
   Add x y -> comp' x (comp' y (ADD c));
   Throw -> FAIL;
   Catch x h -> MARK (comp' h c) (comp' x (UNMARK c))}

comp :: Expr -> Code
comp e =
  comp' e HALT

