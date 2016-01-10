module Test

import Effects
import Effect.State
import Classes.Verified
import Data.List
import Data.Vect
import Data.Fin
import Data.So

import General
import Symbols
import Properties
import Expressions
import Facts

positive : Property
positive = symbol "positive" ()

plusS : Symbol $ BinOp Nat
plusS = record {inheritance = strictOnly [positive]} $ infixs "+" $ BinOp Nat

-- pt1 : List (Expression (Pattern Nat))
-- pt1 = [VarSeq (symbol "vs"), variable "v"]
-- 
ex1 : List (Expression Nat)
ex1 = [1, 2, 3]

-- pt2 : List (Expression (Pattern Nat))
-- pt2 = [VarSeq (symbol "xs"), VarSeq (symbol "ys"), variable "v"]

ex2 : List (Expression Nat)
ex2 = [1, 2, 3, 4, 5]

xx : Symbol Nat
xx = symbol "xx" Nat `withProp` positive

yy : Symbol Nat
yy = symbol "yy" Nat `withProp` positive

xPlusY : Expression Nat
xPlusY = Apply (Variable plusS) $ EList [Variable xx, Variable yy]

one : Expression Nat
one = 1

greater : Symbol $ Relation Nat
greater = infixs ">" $ Relation Nat

x0 : Expression Nat
x0 = variable "x" Nat

y0 : Expression Nat
y0 = variable "y" Nat

ypos : Fact
ypos = Apply (Variable greater) $ EList [y0, Const 0]

xGtY : Fact
xGtY = the (Expression Bool) $ Apply (Variable greater) $ EList [x0, y0]

factsDb : Facts
factsDb = [ypos, xGtY]

showVariable : Expression t -> String
showVariable (Variable sym) = show sym
showVariable _ = "<not a variable>"

test1 : IO ()
test1 = do
  case isApplication xPlusY of
       Nothing => printLn "Not application."
       Just p => do
         let (_ ** op) = topOperator xPlusY
         printLn $ op
         let (_ ** args) = operands xPlusY
         printLn $ args

sqrt : Expression (Tuple [Double] -> Double)
sqrt = variable "sqrt" (Tuple [Double] -> Double)
 
sqr : Expression (Tuple [Double] -> Double)
sqr = Variable $ postfix "^2" (Tuple [Double] -> Double)
 
two : Expression Double
two = 2

zz : Expression Double
zz = Variable $ symbol "z" Double `withProp` positive

cancelSqrt : Expression Double -> (t ** Expression t)
cancelSqrt ex@(Apply (Variable s1) (EList [Apply (Variable s2) (EList [x])])) = 
  if symbolName s1 == "sqrt" && symbolName s2 == "^2"
     then case checkHas positive x of
               Nothing => (Double ** ex)
               Just _ => (_ ** x)
     else (Double ** ex)


