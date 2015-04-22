module Exceptions where

import Prelude hiding (fail)

data Expr = Val Int | Add Expr Expr | Throw | Catch Expr Expr

eval             :: Expr -> Maybe Int
eval (Val n)     =  Just n
eval (Add x y)   =  case eval x of 
                      Just n  -> case eval y of 
                                   Just m  -> Just (n + m)
                                   Nothing -> Nothing
                      Nothing -> Nothing
eval Throw       =  Nothing
eval (Catch x h) =  case eval x of
                       Just n  -> Just n
                       Nothing -> eval h


data Code = HALT | PUSH Int Code | ADD Code |
            FAIL | MARK Code Code | UNMARK Code


comp		    :: Expr -> Code
comp e		    =  comp' e HALT

comp'		    :: Expr -> Code -> Code
comp' (Val n) c     =  PUSH n c
comp' (Add x y) c   =  comp' x (comp' y (ADD c))
comp' Throw c       =  FAIL
comp' (Catch x h) c =  MARK (comp' h c) (comp' x (UNMARK c))

type Stack = [Elem]
data Elem  = VAL Int | HAN Code

exec		                    :: Code -> Stack -> Stack
exec HALT s			    =  s
exec (PUSH n c) s                   =  exec c (VAL n : s)
exec (ADD c) (VAL m : VAL n : s)    =  exec c (VAL (n+m) : s)
exec FAIL s                         =  fail s
exec (MARK c' c) s                  =  exec c (HAN c' : s)
exec (UNMARK c) (VAL n : HAN _ : s) =  exec c (VAL n : s)

fail		     		    :: Stack -> Stack
fail []                             =  []
fail (VAL n : s)     		    =  fail s
fail (HAN c : s)      		    =  exec c s
