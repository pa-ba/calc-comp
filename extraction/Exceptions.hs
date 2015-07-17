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
comp' x c =
  case x of {
   Val n -> PUSH n c;
   Add x1 x2 -> comp' x1 (comp' x2 (ADD c));
   Throw -> FAIL;
   Catch x1 x2 -> MARK (comp' x2 c) (comp' x1 (UNMARK c))}

comp :: Expr -> Code
comp x =
  comp' x HALT

