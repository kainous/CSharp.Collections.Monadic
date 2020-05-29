module Math.Functorial.Functor

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid
import Math.Categorical.Category
import Math.Categorical.Morphism
import Math.Functorial.RawGenFunctor

%default total
%access public export

interface
  RawThinFunctor (f : Type -> Type) where
    map : (a -> b) -> (f a -> f b)

--interface Endofunctor (~>) f => HaskFunctor (f : Type -> Type)

data LiftedFunctor : Type -> Type where
  MkLiftedFunctor  : (f : Type -> Type) -> x -> LiftedFunctor (f x)

data LoweredFunctor : Type -> Type where
  MkLoweredFunctor : (f : Type -> Type) -> x -> LoweredFunctor (f x)

RawThinFunctor f => RawGenFunctor (~>) (~>) (LiftedFunctor f) where
  genMap f x = ?rhs
