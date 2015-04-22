module StateLocal where

import Prelude hiding (fail)

type State = Int

data Expr  = Val Int | Add Expr Expr | Throw | Catch Expr Expr | Get | Put Expr Expr

eval :: Expr -> State -> Maybe (Int, State)
eval (Val n) q     = Just (n, q)
eval (Add x y) q   = case eval x q of 
                       Just (n, q') -> case eval y q' of 
                                         Just (m, q'') -> Just (n + m, q'')
                                         Nothing       -> Nothing
                       Nothing      -> Nothing
eval Throw q       = Nothing
eval (Catch x h) q = case eval x q of
                       Just (n, q') -> Just (n, q')
                       Nothing      -> eval h q
eval Get q         = Just (q, q)
eval (Put x y) q   = case eval x q of
                       Just (n, q') -> eval y n
                       Nothing      -> Nothing


data Code = HALT | PUSH Int Code | ADD Code |
            FAIL | MARK Code Code | UNMARK Code |
            LOAD Code | SAVE Code

comp                :: Expr -> Code
comp e              =  comp' e HALT

comp'               :: Expr -> Code -> Code
comp' (Val n) c     =  PUSH n c
comp' (Add x y) c   =  comp' x (comp' y (ADD c))
comp' Throw c       =  FAIL
comp' (Catch x h) c =  MARK (comp' h c) (comp' x (UNMARK c))
comp' Get c         =  LOAD c
comp' (Put x y) c   =  comp' x (SAVE (comp' y c))


type Conf  = (Stack, State)

type Stack = [Elem]

data Elem  = VAL Int | HAN Code State


exec                                     :: Code -> Conf -> Conf
exec HALT (s, q)                         =  (s, q)
exec (PUSH n c) (s, q)                   =  exec c (VAL n : s, q)
exec (ADD c) (VAL m : VAL n : s, q)      =  exec c (VAL (n + m) : s, q)
exec FAIL (s, q)                         =  fail s
exec (MARK h c) (s, q)                   =  exec c (HAN h q : s, q)
exec (UNMARK c) (VAL n : HAN _ _ : s, q) =  exec c (VAL n : s, q)
exec (LOAD c) (s, q)                     =  exec c (VAL q : s, q)
exec (SAVE c) (VAL n : s, q)             =  exec c (s, n)

fail                                     :: Stack -> Conf
fail []                                  =  ([],0)
fail (VAL n : s)                         =  fail s
fail (HAN h q : s)                       =  exec h (s, q)
