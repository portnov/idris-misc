module Properties

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

exProperties : Expression t -> List Property
exProperties (Variable sym) = symbolProps sym
exProperties (Apply (Variable f) (EList xs)) with (inheritance f)
  | Inherit condition what =
      filter toInherit props
        where
          toInherit p = case condition of
                             AllChild => all (\props => p `elem` props) $ map exProperties xs
                             AnyChild => any (\props => p `elem` props) $ map exProperties xs
          props = case what of
                       NoProps => []
                       AllProps => foldr union [] $ map exProperties xs
                       Only lst => lst
exProperties _ = []

class HasProperties t where
  getProperties : t -> List Property

instance HasProperties (Symbol t) where
  getProperties = symbolProps

instance HasProperties (Expression t) where
  getProperties = exProperties

data Has : HasProperties t => Property -> (x : t) -> Type where
  MkHas : HasProperties t => (p : Property) -> (x : t) -> (p `EqElem` getProperties x) -> Has p x

checkHas : HasProperties t => (p : Property) -> (x : t) -> Maybe (Has p x)
checkHas p x =
  case isEqElem p (getProperties x) of
       Nothing => Nothing
       Just prf => Just $ MkHas p x prf


