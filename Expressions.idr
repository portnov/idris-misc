module Expressions

import Effects
import Effect.State
import Classes.Verified
import Data.List
import Data.Vect
import Data.Fin
import Data.So

import General
import Symbols

data Expression : Type -> Type where
  Variable: Symbol t -> Expression t
  Const: Show t => t -> Expression t
  Apply: Expression (s -> t) -> Expression s -> Expression t
  EList: List (Expression t) -> Expression (List t)
  Lambda: Symbol t -> Expression s -> Expression (t -> s)

typeOfEx : {t :Type} -> (x : Expression t) -> Type
typeOfEx {t} _ = t

data IsApplication : Expression t -> Type where
  MkIsApplication : IsApplication (Apply f arg)

isApplication : (ex : Expression t) -> Maybe (IsApplication ex)
isApplication (Apply f x) = Just MkIsApplication
isApplication _ = Nothing

symbols : Expression t -> GTuple Symbol
symbols (Variable s) = [s]
symbols (Const _) = []
symbols (Apply f x) = symbols f `union` symbols x
symbols (EList xs) = foldr union [] $ map symbols xs
symbols (Lambda l x) = [l] `union` symbols x

instance Eq t => Eq (Expression t) where
  (Variable x) == (Variable y) = x == y
  (Const x) == (Const y) = x == y
  (Apply (Variable f1) x) == (Apply (Variable f2) y) = (f1 == f2) && (x == y)
  (EList xs) == (EList ys) = xs == ys
  (Lambda l1 x) == (Lambda l2 y) = (l1 == l2) && (x == y)
  _ == _ = False

intercalateS : String -> List String -> String
intercalateS sep xs = pack $ intercalate (unpack sep) (Functor.map unpack xs)

mutual 

  instance Show (Expression t) where
    show (Variable s) = show s
    show (Const c) = show c
    show (Apply (Variable sym) (EList xs)) =
      case fixity sym of
           InfixS => "(" ++ intercalateS (" " ++ show sym ++ " ") (Functor.map show xs) ++ ")"
           Prefix => show sym ++ " " ++ show xs
           Postfix => show xs ++ " " ++ show sym
    show (Apply (Variable sym) x) = 
      case fixity sym of
           Postfix => "(" ++ show x ++ " " ++ show sym ++ ")"
           otherwise => "(" ++ show sym ++ " " ++ show x ++ ")"
    show (Apply f x) = "(" ++ show f ++ " " ++ show x ++ ")"
    show (EList xs) = "[" ++ intercalateS ", " (Functor.map show xs) ++ "]"
    show (Lambda l x) = "(λ" ++ show l ++ " => " ++ "<>" ++ ")"

total operands : (ex : Expression t) -> {auto prf : IsApplication ex} -> (s ** List (Expression s))
operands (Apply _ (EList xs)) {prf=MkIsApplication} = (_ ** xs)
operands (Apply _ xs) {prf=MkIsApplication} = (_ ** [xs])

total topOperator : (ex : Expression t) -> {auto prf : IsApplication ex} -> (s ** Expression (s -> t))
topOperator (Apply f _) {prf=MkIsApplication} = (_ ** f)

variable : String -> (t : Type) -> Expression t
variable v t = Variable (symbol v t)

BinOp : Type -> Type
BinOp t = t -> t -> t

binOp : String -> (t : Type) -> Expression (BinOp t)
binOp name t = Variable $ infixs name $ BinOp t

MultiOp : Type -> Type
MultiOp t = List t -> t

multiOp : String -> (t : Type) -> Expression (MultiOp t)
multiOp name t = Variable $ infixs name $ MultiOp t

Relation : Type -> Type
Relation t = t -> t -> Bool

instance (Num t, Show t) => Num (Expression t) where
  fromInteger i = Const $ fromInteger i

  (Const x) + (Const y) = Const (x+y)
  e1 + e2 = Apply (multiOp "+" $ typeOfEx e1) $ EList [e1, e2]

  (Const x) * (Const y) = Const (x*y)
  e1 * e2 = Apply (multiOp "*" $ typeOfEx e1) $ EList [e1, e2]

