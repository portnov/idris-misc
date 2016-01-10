module Patterns

import General
import Symbols
import Expressions

mutual
  data Pattern : Type -> Type where
    Var : String -> Pattern t
    VarSeq : String -> Pattern (PTuple ts)
    Fixed : Expression t -> Pattern t
    PList : PTuple ts -> Pattern (PTuple ts)
    PApply : Pattern (PTuple ts -> t) -> Pattern (PTuple ts) -> Pattern t

  PTuple : List Type -> Type
  PTuple ts = FTuple Pattern ts

tt1 : Pattern t
tt1 = PList [Fixed 1, VarSeq "__", Var "x"]
