
module Test2

import Data.List
import Data.Vect
import Data.Fin

import General

tt1 : HList Num
tt1 = [MkSome 1, MkSome 2]

f1 : Some Num -> Some Num
f1 (MkSome x) = MkSome (x*x)

data MyData = C1 | C2 Int Int

data IsC2 : MyData -> Type where
  MkIsC2 : IsC2 (C2 x y)

total f : (x : MyData) -> {prf: IsC2 x} -> Int
f (C2 x _) {prf=MkIsC2} = x

vect : Nat -> Type
vect n = Vect n Type

vt1 : vect 3
vt1 = [Nat, String, MyData]

insert : Eq a => a -> Vect n a -> (m ** Vect m a)
insert x [] = (_ ** [x])
insert x (y :: ys) =
  if x == y
     then (_ ** (y :: ys))
     else let (k ** r) = insert x ys
          in (S k ** (y :: r))

data Pattern : Number -> (t : Type) -> Type where
  Fixed : Eq t => t -> Pattern One t
  Var : String -> Pattern One t
  VarSeq : String -> Pattern Many t

matchList : Eq t => List (Pattern n t) -> List (String, t)

