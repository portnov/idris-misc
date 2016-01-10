module Facts

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

Fact : Type
Fact = Expression Bool

Facts : Type
Facts = List Fact

factSymbols : Fact -> GTuple Symbol
factSymbols ex = symbols ex

symbolFacts : Symbol t -> Facts -> Facts
symbolFacts sym db = filter (\f => sym `elem` factSymbols f) db

