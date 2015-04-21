module LambdaCBName where

import qualified Prelude

data Expr =
   Val Prelude.Int
 | Add Expr Expr
 | Var Prelude.Int
 | Abs Expr
 | App Expr Expr

data Code =
   PUSH Prelude.Int Code
 | ADD Code
 | RET
 | LOOKUP Prelude.Int Code
 | APP Code Code
 | ABS Code Code
 | HALT

comp' :: Expr -> Code -> Code
comp' e c =
  case e of {
   Val n -> PUSH n c;
   Add x y -> comp' x (comp' y (ADD c));
   Var i -> LOOKUP i c;
   Abs x -> ABS (comp' x RET) c;
   App x y -> comp' x (APP (comp' y RET) c)}

comp :: Expr -> Code
comp e =
  comp' e HALT

