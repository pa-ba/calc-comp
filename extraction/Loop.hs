module Loop where

import qualified Prelude

data Expr =
   Val Prelude.Int
 | Add Expr Expr
 | Get

data Stmt =
   Put Expr
 | Seqn Stmt Stmt
 | While Expr Stmt

data Code =
   PUSH Prelude.Int Code
 | ADD Code
 | GET Code
 | PUT Code
 | LOOP
 | JMP Code Code
 | ENTER Code
 | HALT

compE :: Expr -> Code -> Code
compE x c =
  case x of {
   Val n -> PUSH n c;
   Add x1 x2 -> compE x1 (compE x2 (ADD c));
   Get -> GET c}

compS :: Stmt -> Code -> Code
compS x c =
  case x of {
   Put x0 -> compE x0 (PUT c);
   Seqn x1 x2 -> compS x1 (compS x2 c);
   While x1 x2 -> ENTER (compE x1 (JMP c (compS x2 LOOP)))}

comp :: Stmt -> Code
comp x =
  compS x HALT

