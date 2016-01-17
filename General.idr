module General

import Effects
import Effect.State
import Classes.Verified
import Data.List
import Data.Vect
import Data.Fin
import Data.So

data Some : (cls : Type -> Type) -> Type where
  MkSome : cls a => a -> Some cls

HList : (cls : Type -> Type) -> Type
HList cls = List (Some cls)

hl1 : HList Show
hl1 = [MkSome 1, MkSome "2"]

class HasRepresentation r a where
  repr : a -> r

reprEq : (HasRepresentation r a, HasRepresentation r b, Eq r) => {r : Type} -> a -> b -> Bool
reprEq {r} x y = the r (repr x) == repr y

class GenEq (f : Type -> Type) where
  genEq : f a -> f b -> Bool

gets : (x -> a) -> Eff a [STATE x]
gets fn = do
  x <- get
  return $ fn x

typeOf : {t : Type} -> (x : t) -> Type
typeOf {t} _ = t

namespace FTuple
  data FTuple : (f : Type -> Type) -> List Type -> Type where
    Nil : FTuple f []
    (::) : f t -> FTuple f ts -> FTuple f (t :: ts)

  elem : GenEq f => f t -> FTuple f ts -> Bool
  elem x [] = False
  elem x (y :: ys) =
    if x `genEq` y
       then True
       else elem x ys

  insert : (GenEq f, Show t) =>  f t -> FTuple f ts -> Either (FTuple f ts) (FTuple f (t :: ts))
  insert x xs =
    if x `elem` xs
       then Left xs
       else Right (x :: xs)

  map : ({t : Type} -> f t -> r) -> FTuple f ts -> List r
  map _ [] = []
  map fn (x :: xs) = fn x :: map fn xs

  (++) : FTuple f ts1 -> FTuple f ts2 -> FTuple f (ts1 ++ ts2)
  [] ++ y = y
  (x :: xs) ++ ys = x :: xs ++ ys

--   union : GenEq f => FTuple f ts1 -> FTuple f ts2 -> FTuple f ts3
--   union [] [] = []
--   union [] ys = ys
--   union xs [] = xs
--   union (x :: xs) (y :: ys) =
--     if x `genEq` y
--        then x :: union xs ys
--        else x :: y :: union xs ys

namespace GTuple
  data GTuple : (f : Type -> Type) -> Type where
    Nil : GTuple f 
    (::) : f t -> GTuple f -> GTuple f 

  union : GenEq f => GTuple f -> GTuple f -> GTuple f 
  union [] [] = []
  union [] ys = ys
  union xs [] = xs
  union (x :: xs) (y :: ys) =
    if x `genEq` y
       then x :: union xs ys
       else x :: y :: union xs ys

  elem : GenEq f => f t -> GTuple f -> Bool
  elem x [] = False
  elem x (y :: ys) =
    if x `genEq` y
       then True
       else elem x ys

class TryShow t where
  tryShow : {t : Type} -> (x : t) -> Maybe String

instance TryShow Int where
  tryShow x = Just $ show x

instance TryShow Nat where
  tryShow x = Just $ show x

instance TryShow String where
  tryShow x = Just x

instance TryShow (a -> b) where
  tryShow _ = Nothing

data EqElem : Eq a => a -> List a -> Type where
  Here : Eq a => {x,y : a} -> So (x == y) -> EqElem x (y :: ys)
  There : Eq a => {x,y : a} -> EqElem x xs -> EqElem x (y :: xs)

isEqElem : Eq a => (x : a) -> (xs : List a) -> Maybe (EqElem x xs)
isEqElem _ [] = Nothing
isEqElem x (y :: ys) =
  case choose (x == y) of
      Left oh => Just $ Here oh
      Right _ => case isEqElem x ys of
                      Nothing => Nothing
                      Just eq => Just $ There eq

data Number : Type where
  Zero : Number
  One : Number
  Many : Number
  (:+) : Number -> Number -> Number

infixr 8 :+

instance Show Number where
  show Zero = "0"
  show One = "1"
  show Many = "N"
  show (x :+ y) = show x ++ " + " ++ show y

data Sequence : Number -> Type -> Type where
  Nil : Sequence Zero t
  Single : t -> Sequence One t
  Several : t -> Sequence Many t
  (::) : Sequence n t -> Sequence m t -> Sequence (n :+ m) t

instance Show t => Show (Sequence n t) where
  show Nil = "[]"
  show (Single x) = show x
  show (Several x) = show x
  show (x :: xs) = show x ++ " :: " ++ show xs

sq1 : Sequence (One :+ Many :+ One :+ Zero) String
sq1 = [Single "x", Several "xs", Single "_"]

ft1 : FTuple Maybe [Int, String]
ft1 = [Just 1, Just "2"]

gt1 : GTuple Maybe
gt1 = [Just 1, Just "2"]

ftt1 : List Int
ftt1 = map f ft1
  where
    f : {t : Type} -> Maybe t -> Int
    f Nothing = 1
    f _ = 0

