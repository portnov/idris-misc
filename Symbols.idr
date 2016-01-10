module Symbols

import Data.List
import Data.Vect
import Data.Fin

import General

data SymbolFixity = Prefix | Postfix | InfixS

instance Eq SymbolFixity where
  Prefix == Prefix = True
  Postfix == Postfix = True
  InfixS == InfixS = True
  _ == _ = False

data InheritCondition = AllChild | AnyChild

mutual

  data InheritProps = NoProps | AllProps | Only (List Property)

  record Inheritance where
    constructor Inherit
    condition : InheritCondition
    inheritProps : InheritProps

  record Symbol t where
    constructor MkSymbol
    symbolName : String
    symbolType : Type
    fixity : SymbolFixity
    symbolProps : List Property
    inheritance : Inheritance

  Property : Type
  Property = Symbol ()

instance Show (Symbol t) where
  show sym = symbolName sym

instance Eq (Symbol t) where
  x == y = symbolName x == symbolName y

instance GenEq Symbol where
  genEq x y = symbolName x == symbolName y

instance TryShow (Symbol t) where
  tryShow s = Just $ show s

zeroInheritance : Inheritance
zeroInheritance = Inherit AllChild NoProps

strictAll : Inheritance
strictAll = Inherit AllChild AllProps

looseAll : Inheritance
looseAll = Inherit AnyChild AllProps

strictOnly : List Property -> Inheritance
strictOnly props = Inherit AllChild $ Only props

looseOnly : List Property -> Inheritance
looseOnly props = Inherit AnyChild $ Only props

symbol : String -> (t : Type) -> Symbol t
symbol s t = MkSymbol s t Prefix [] zeroInheritance

postfix : String -> (t : Type) -> Symbol t
postfix s t = MkSymbol s t Postfix [] zeroInheritance

infixs : String -> (t : Type) -> Symbol t
infixs s t = MkSymbol s t InfixS [] zeroInheritance

has : Symbol t -> Property -> Bool
has sym prop = prop `elem` symbolProps sym

withProp : Symbol t -> Property -> Symbol t
withProp sym prop = record {symbolProps = prop :: symbolProps sym} sym

