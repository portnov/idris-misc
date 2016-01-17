module Patterns

import General
import Symbols
import Expressions

singleOrList : Number -> Type -> Type
singleOrList One t = t
singleOrList _ t = List t

mutual 
  data APattern : Type -> Type where
    MkPattern : Pattern n t -> APattern t 

  data Pattern : Number -> Type -> Type where
    Nil : Pattern Zero (List t)
    Var : String -> Pattern One t
    VarSeq : String -> Pattern Many (List t)
    Fixed : Expression t -> Pattern One t
    PApply : Pattern One (s -> t) -> Pattern One s -> Pattern One t
    (::) : Pattern n (singleOrList n t) -> Pattern m (singleOrList m t) -> Pattern (n :+ m) (List t)

data Match : Type where
  Bind : String -> (t : Type) -> Expression t -> Match

Matches : Type
Matches = List Match

tt1 : Pattern (One :+ Many :+ One :+ Zero) (List Nat)
tt1 = [Fixed 1, VarSeq "__", Var "x"]

match : {t : Type} -> {n : Number} -> Pattern n (singleOrList n (Expression t)) -> singleOrList n (Expression t) -> Matches
match Patterns.Nil List.Nil = List.Nil
match {t} (Var v) x = [Bind v t x]


