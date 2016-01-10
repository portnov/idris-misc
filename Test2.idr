
module Test2

import Data.List
import Data.Vect
import Data.Fin

data Some : (cls : Type -> Type) -> Type where
  MkSome : cls a => a -> Some cls

HList : (cls : Type -> Type) -> Type
HList cls = List (Some cls)

tt1 : HList Num
tt1 = [MkSome 1, MkSome 2]

f1 : Some Num -> Some Num
f1 (MkSome x) = MkSome (x*x)

tt2 : HList Num
tt2 = map f1 tt1

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

class TryShow a where
  tryShow : a -> Maybe String

instance TryShow Int where
  tryShow x = Just $ show x

instance TryShow (a -> b) where
  tryShow _ = Nothing

data Expr : Type where
  Val : Int -> Expr
  Func : (Int -> Int) -> Expr
  App : Expr -> Expr -> Expr

instance TryShow Expr where
  tryShow (Val x) = Just $ show x
  tryShow (Func _) = Nothing
  tryShow (App f x) = do
    sf <- tryShow f
    sx <- tryShow x
    return $ sf ++ " " ++ sx

