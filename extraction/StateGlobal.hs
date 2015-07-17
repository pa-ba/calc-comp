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
comp' x c =
  case x of {
   Val n -> PUSH n c;
   Add x1 x2 -> comp' x1 (comp' x2 (ADD c));
   Throw -> FAIL;
   Catch x1 x2 -> MARK (comp' x2 c) (comp' x1 (UNMARK c));
   Get -> LOAD c;
   Put x1 x2 -> comp' x1 (SAVE (comp' x2 c))}

comp :: Expr -> Code
comp x =
  comp' x HALT

