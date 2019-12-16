||| Test

module Prelude.Functor

import Builtins
import Data.Semigroupoid

infix 4 ~>
infixr 4 <$>
infixl 3 <*>
infixl 1 >>=
--infixl 6 >>

interface Morphism a b where
  Source : a
  Target : b

(~>) : Type -> Type -> Type


--Morphism (~>) where
--  Source = ?rhs
--  Target = ?rhs2


interface Functor' (f : Type -> Type) where
  map : (func : a -> b) -> f a -> f b

(<$>) : Functor' f => (func : a -> b) -> f a -> f b
func <$> x = map func x

data Const

--interface Functor' f => Functor (f : Type -> Type) where
--  identityPreservation    : map id = id
--  compositionPreservation : map (f >> g) = (map f) >> (map g)

--interface ContravariantFunctor' (func : Type -> Type) where
--  contramap : (func : a -> b) -> f b -> f a

--interface ContravariantFunctor f => ContravariantFunctor' (func : Type -> Type) where
--  identityPreservation    : contramap id = id
--  compositionPreservation : contramap (f >> g) = (contramap g) >> (contramap f)

DirectedGraph Type where
  --attach (HomSet f) (HomSet g) = HomSet (\x => g (f x))

--Semigroupoid' (~>) where
--Semigroupoid (~>) where
  -- This associativity test would require funext, which would require univalance
--  associative f g h = believe_me ((f >> (g >> h)) = ((f >> g) >> h))

--Id : a ~> a
--Id = HomSet id

--Category' (~>) where
--  unit {a} = Id

--Category (~>) where
--  leftUnitary (Mor f) = believe_me () ?rhs

    --leftUnitary  : {a, b : obj} -> (f : arr a b) -> unit a >> f         = f
    --rightUnitary : {a, b : obj} -> (f : arr a b) ->      f >> unit b = f

--test0 : a ~> a
--test0 = Id >> Id


{-interface Functor {a, b : Type} -> (f : a ~> b) where
  map : (func : a -> b) -> f a -> f b

(<$>) : Functor f => (func : a -> b) -> f a -> f b
func <$> x = map func x

interface Functor f => Applicative (f : Type -> Type) where
  wrap : a -> f a
  (<*>) : f (a -> b) -> f a -> f b

interface Applicative m => Monad (m : Type -> Type) where
  (>>=) : m a -> ((result : a) -> m b) -> m b
  join : m (m a) -> m a

  x >>= f = join (f <$> x)
  join x = x >>= id

Functor Id where
  map fn (Id a)-}



--(>>) : Monad m => (a -> m b) -> (b -> m c) -> a -> m c
--f >> g = \x -> f x >>= g
