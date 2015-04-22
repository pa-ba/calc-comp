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
compE e c =
  case e of {
   Val n -> PUSH n c;
   Add x y -> compE x (compE y (ADD c));
   Get -> GET c}

compS :: Stmt -> Code -> Code
compS e c =
  case e of {
   Put e0 -> compE e0 (PUT c);
   Seqn e1 e2 -> compS e1 (compS e2 c);
   While e1 e2 -> ENTER (compE e1 (JMP c (compS e2 LOOP)))}

comp :: Stmt -> Code
comp e =
  compS e HALT

