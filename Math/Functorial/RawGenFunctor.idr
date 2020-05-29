module Math.Functorial.Functor

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid
import Math.Categorical.Category

%default total
%access public export

interface
  ( RawCategory cat1
  , RawCategory cat2) =>

  RawGenFunctor
    (cat1 : obj1 -> obj1 -> Type)
    (cat2 : obj2 -> obj2 -> Type)
    (f : obj1 -> obj2) where
  genMap : cat1 a b -> cat2 (f a) (f b)

interface (RawCategory a, RawGenFunctor a a f) => Endofunctor (a : obj -> obj -> Type) (f : obj -> obj) where
