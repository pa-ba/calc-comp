module LambdaExceptions where

import qualified Prelude

data Expr =
   Val Prelude.Int
 | Add Expr Expr
 | Throw
 | Catch Expr Expr
 | Var Prelude.Int
 | Abs Expr
 | App Expr Expr

data Code =
   PUSH Prelude.Int Code
 | ADD Code
 | LOOKUP Prelude.Int Code
 | RET
 | APP Code
 | ABS Code Code
 | ASSERT_NUM Code
 | ASSERT_CLO Code
 | UNMARK Code
 | MARK Code Code
 | FAIL
 | HALT

comp' :: Expr -> Code -> Code
comp' e c =
  case e of {
   Val n -> PUSH n c;
   Add x y -> comp' x (ASSERT_NUM (comp' y (ADD c)));
   Throw -> FAIL;
   Catch x y -> MARK (comp' y c) (comp' x (UNMARK c));
   Var i -> LOOKUP i c;
   Abs x -> ABS (comp' x RET) c;
   App x y -> comp' x (ASSERT_CLO (comp' y (APP c)))}

comp :: Expr -> Code
comp e =
  comp' e HALT

