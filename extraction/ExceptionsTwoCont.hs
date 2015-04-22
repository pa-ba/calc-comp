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
comp' e sc fc =
  case e of {
   Val n -> PUSH n sc;
   Add x y -> comp' x (comp' y (ADD sc) (POP fc)) fc;
   Throw -> fc;
   Catch x h -> comp' x sc (comp' h sc fc)}

comp :: Expr -> Code
comp e =
  comp' e HALT HALT

