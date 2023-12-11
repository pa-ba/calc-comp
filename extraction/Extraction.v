Require Extraction.


Extraction Language Haskell.

Extract Inductive nat => "Prelude.Int" ["0" "succ"] "(\fO fS n -> if n==0 then fO () else fS (n-1))".


Require Arith.
Extraction "Arith.hs" Arith.comp.

Require Exceptions.
Extraction "Exceptions.hs" Exceptions.comp.

Require ExceptionsTwoCont.
Extraction "ExceptionsTwoCont.hs" ExceptionsTwoCont.comp.

Require StateGlobal.
Extraction "StateGlobal.hs" StateGlobal.comp.

Require StateLocal.
Extraction "StateLocal.hs" StateLocal.comp.

Require StateGlobalSeq.
Extraction "StateGlobalSeq.hs" StateGlobalSeq.comp.

Require Lambda.
Extraction "Lambda.hs" Lambda.comp.

Require LambdaExceptions.
Extraction "LambdaExceptions.hs" LambdaExceptions.comp.

Require LambdaCBName.
Extraction "LambdaCBName.hs" LambdaCBName.comp.

Require LambdaCBNeed.
Extraction "LambdaCBNeed.hs" LambdaCBNeed.comp.

Require Loop.
Extraction "Loop.hs" Loop.comp.
