module StateGlobalSeq where

import qualified Prelude

data Expr =
   Val Prelude.Int
 | Add Expr Expr
 | Throw
 | Catch Expr Expr
 | Seq Expr Expr
 | Get
 | Put Expr

data Code =
   HALT
 | PUSH Prelude.Int Code
 | ADD Code
 | FAIL
 | MARK Code Code
 | UNMARK Code
 | LOAD Code
 | POP Code
 | SAVE Code

comp' :: Expr -> Code -> Code
comp' x c =
  case x of {
   Val n -> PUSH n c;
   Add x1 x2 -> comp' x1 (comp' x2 (ADD c));
   Throw -> FAIL;
   Catch x1 x2 -> MARK (comp' x2 c) (comp' x1 (UNMARK c));
   Seq x1 x2 -> comp' x1 (POP (comp' x2 c));
   Get -> LOAD c;
   Put x' -> comp' x' (SAVE c)}

comp :: Expr -> Code
comp x =
  comp' x HALT

