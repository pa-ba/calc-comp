module ExceptionsTwoCont where

import qualified Prelude

data Expr =
   Val Prelude.Int
 | Add Expr Expr
 | Throw
 | Catch Expr Expr

data Code =
   PUSH Prelude.Int Code
 | ADD Code
 | POP Code
 | HALT

comp' :: Expr -> Code -> Code -> Code
comp' x sc fc =
  case x of {
   Val n -> PUSH n sc;
   Add x0 y -> comp' x0 (comp' y (ADD sc) (POP fc)) fc;
   Throw -> fc;
   Catch x1 x2 -> comp' x1 sc (comp' x2 sc fc)}

comp :: Expr -> Code
comp x =
  comp' x HALT HALT

