module Misc

import Effects
import Effect.State
import Classes.Verified
import Data.List
import Data.Vect
import Data.Fin
import Data.So

import General
import Symbols
import Expressions

-- data Pattern : (t: Type) -> Type where
--   Wild : Pattern t
--   WildSeq : Pattern t
--   Fixed : Expression t -> Pattern t
-- 
-- instance Show t => Show (Pattern t) where
--   show Wild = "_"
--   show WildSeq = "__"
--   show (Fixed f) = show f
-- 
-- wild : Expression (Pattern t)
-- wild = Const Wild


data Match t = Map Symbol (Expression t)

Matches : Type -> Type
Matches t = List (Match t)

-- op2 : String -> Expression (Pattern t) -> Expression (Pattern t) -> Expression (Pattern t)
-- op2 o e1 e2 = Apply (Variable (infixs o)) $ EList [e1, e2]

eval1 : Expression t -> Symbol -> Expression t -> Expression t
eval1 (Variable v) s val with (v == s)
  | True = val
  | _ = Variable v
eval1 (Apply f a) s val = Apply f (eval1 a s val)
eval1 (Const c) _ _ = Const c
eval1 (EList lst) s val = EList $ map (\x => eval1 x s val) lst
eval1 (Lambda l x) s val = Lambda l (eval1 x s val)

-- patIsSeq : Expression (Pattern t) -> Bool
-- patIsSeq (Const WildSeq) = True
-- patIsSeq (VarSeq _) = True
-- patIsSeq _ = False

lastGood : List (Maybe a) -> Maybe a
lastGood [] = Nothing
lastGood (Nothing :: xs) = lastGood xs
lastGood ((Just x) :: xs) with (lastGood xs)
  | Nothing = Just x
  | y = y

firstGood : List (Maybe a) -> Maybe a
firstGood [] = Nothing
firstGood (Nothing :: xs) = firstGood xs
firstGood ((Just x) :: _) = Just x

allGood : List (Maybe a) -> Maybe (List a)
allGood [] = Just []
allGood (Nothing :: xs) = Nothing
allGood ((Just x) :: xs) with (allGood xs)
  | Nothing = Nothing
  | Just ys = Just (x :: ys)

lookupVar : Symbol -> Matches t -> Maybe (Expression t)
lookupVar k [] = Nothing
lookupVar k ((Map key val) :: xs) with (k == key)
  | True = Just val
  | _ = lookupVar k xs


appendMatches : Eq t => Match t -> Maybe (Matches t) -> Maybe (Matches t)
appendMatches _ Nothing = Nothing
appendMatches (Map k v) (Just []) = Just [Map k v]
appendMatches (Map k v) (Just vs) with (lookupVar k vs)
  | Nothing = Just $ Map k v :: vs
  | Just v' = if v == v'
                 then Just vs
                 else Nothing

-- matchList : Eq t => List (Expression (Pattern t)) -> List (Expression t) -> Maybe (Matches t)
-- matchList [] [] = Just []
-- -- matchList ps xs with (length (filter patIsSeq ps) == 0 && length ps /= length xs)
-- --   | True = Nothing
-- matchList [] _ = Nothing
-- matchList [Const WildSeq] [] = Just []
-- matchList (Const WildSeq :: ps) es@(_::_) = lastGood [matchList ps l | l <- tails es]
-- matchList (Const Wild :: ps) (_ :: es) = matchList ps es
-- matchList (Variable v :: ps) (e :: es) = appendMatches (Map v e) (matchList ps es)
-- matchList [VarSeq _] [] = Just []
-- matchList (VarSeq v :: ps) (e :: xs) with (isLTE (length ps) (length xs))
--   | Yes prf = let m = length xs - length ps + 1
--               in helper ps xs m
--                 where helper ps xs m with (isLTE 1 m)
--                        | No _ = appendMatches (Map v e) (matchList ps xs)
--                        | Yes prf1 = appendMatches (Map v (EList (List.take m (e::xs))))
--                                                   (matchList ps $ drop m (e::xs))
--   | No _ = matchList ps (e::xs)
-- matchList (Const (Fixed p) :: ps) (e :: es) =
--   if p == e
--      then matchList ps es
--      else Nothing
