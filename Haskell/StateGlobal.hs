module StateGlobal where

import qualified Prelude

data Expr =
   Val Prelude.Int
 | Add Expr Expr
 | Throw
 | Catch Expr Expr
 | Get
 | Put Expr Expr

data Code =
   HALT
 | PUSH Prelude.Int Code
 | ADD Code
 | FAIL
 | MARK Code Code
 | UNMARK Code
 | LOAD Code
 | SAVE Code

comp' :: Expr -> Code -> Code
comp' e c =
  case e of {
   Val n -> PUSH n c;
   Add x y -> comp' x (comp' y (ADD c));
   Throw -> FAIL;
   Catch x h -> MARK (comp' h c) (comp' x (UNMARK c));
   Get -> LOAD c;
   Put x y -> comp' x (SAVE (comp' y c))}

comp :: Expr -> Code
comp e =
  comp' e HALT

