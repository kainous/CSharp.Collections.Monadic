module Math.Functorial.Bifunctor

import Builtins
import Math.Categorical.Category

%default total
%access public export

interface (RawCategory cat1, RawCategory cat2, RawCategory cat3) =>
  RawGenericBifunctor
    (f : obj1 -> obj2 -> obj3)
    (cat1 : obj1 -> obj1 -> Type)
    (cat2 : obj2 -> obj2 -> Type)
    (cat3 : obj3 -> obj3 -> Type) where
  bimap : cat1 a1 b1 -> cat2 a2 b2 -> cat3 (f a1 a2) (f b1 b2)

interface (RawCategory cat1, RawCategory cat2, RawCategory cat3) =>
  RawGenericProfunctor
    (f : obj1 -> obj2 -> obj3)
    (cat1 : obj1 -> obj1 -> Type)
    (cat2 : obj2 -> obj2 -> Type)
    (cat3 : obj3 -> obj3 -> Type) where
  dimap : cat1 b1 a1 -> cat2 a2 b2 -> cat3 (f a1 a2) (f b1 b2)

RawGenericBifunctor Pair where
  bimap f g (x, y) = (f x, g y) -- (f a, f b)

RawGenericBifunctor Either where
  bimap f g (Left x)  = Left  (f x)
  bimap f g (Right y) = Right (g y)
