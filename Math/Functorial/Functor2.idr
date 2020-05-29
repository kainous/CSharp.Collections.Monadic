module Math.Functorial.Functor2

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid
import Math.Categorical.Category
--import Math.Categorical.Morphism

infixr 4 ~>

data Morphism a b = Mor (a -> b)

(~>) : Type -> Type -> Type
(~>) = Morphism

Magmoid (~>) where
  compose (Mor f) (Mor g) = Mor (f >> g)

RawSemigroupoid (~>) where
RawCategory (~>) where
  id = Mor id

interface
  ( RawCategory cat1
  , RawCategory cat2) =>

  RawGenFunctor
    (cat1 : obj1 -> obj1 -> Type)
    (cat2 : obj2 -> obj2 -> Type)
    (f : obj1 -> obj2) where
  genMap : cat1 a b -> cat2 (f a) (f b)

interface (RawCategory cat1, RawCategory cat2) =>
  RawGenCofunctor
    (f : obj1 -> obj2)
    (cat1 : obj1 -> obj1 -> Type)
    (cat2 : obj2 -> obj2 -> Type) where
  genComap : cat1 b a -> cat2 (f a) (f b)

interface RawThinFunctor (f : Type -> Type) where
  map : (a -> b) -> (f a -> f b)

RawThinFunctor f => RawGenFunctor (~>) (~>) f where
  genMap (Mor g) = Mor <| map g


infixr 4 !>, <!, $>, <$

-- We use the notation !> to mean "unwrap, then apply, then wrap"

(<!) : RawThinFunctor w => (a -> b) -> w a -> w b
(<!) = map

(!>) : RawThinFunctor w => w a -> (a -> b) -> w b
(!>) = flip map
