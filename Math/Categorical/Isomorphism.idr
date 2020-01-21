module Math.Categorical.Isomorphism

import Builtins
import Math.Functorial.Functor
import Math.Categorical.Morphism
import Math.Categorical.Magmoid
import Math.Functorial.Functor
import Math.Categorical.Morphism
import Math.Categorical.Semigroupoid
import Math.Categorical.Category

%default total
%access public export

infixl 4 <~>, ==

-- Polykinded functors wherein KFunctor 2 = bifunctor. (see Data.Polykinded.Functor)

data Optional a = None | OneOf a

interface CategoryEx obj (mor : obj -> obj -> Type) | mor where
  id : mor a a
  compose : mor a b -> mor b c -> mor a c

interface (RawCategory xcat, RawCategory ycat) => RawGenFunctor (f : xobj -> yobj) (xcat : xobj -> xobj -> Type) (ycat : yobj -> yobj -> Type) | f where
  map : xcat a b -> ycat (f a) (f b)

RawGenFunctor Optional (~>) (~>) where
  map (Mor f) =
    Mor (\x => case x of
               None => None
               OneOf x' => OneOf (f x'))

interface RawGenFunctor f a a => Endofunctor (f : obj -> obj) (a : obj -> obj -> Type) where

Endofunctor Optional (~>) where

-- should 'g' be representable?
{-interface (Functor f, Functor g) => Adjoint f g where
  unit   : x -> g (f x)
  counit : g (f x) -> x
  leftAdjunct  : (f a -> b) -> a -> g b
  rightAdjunct : (a -> g b) -> f a -> b

  unit   = leftAdjunct id
  counit = rightAdjunct id
  leftAdjunct  f = map f << unit
  rightAdjunct f = counit << map f-}

interface Isomorphism a b where
  constructor MkIso
  to   : a ~> b
  from : b ~> a

Magmoid Isomorphism where
  compose (MkIso to from) (MkIso to' from') = MkIso (to >> to') (from' >> from)

RawSemigroupoid Isomorphism where

-- Second parameter should be "Representable"
interface (RawFunctor f, RawFunctor g) => Adjunction f g where
  unit   : x -> g (f x)
  counit : f (g x) -> x
  leftAdjunct  : (f a -> b) -> a -> g b
  rightAdjunct : (a -> g b) -> f a -> b

  unit   = leftAdjunct id
  counit = rightAdjunct id
  leftAdjunct  = map f << unit
  rightAdjunct = counit << map f

-- Can we find the Adjunctions and then prove that unit and counit is id for Isomorphism???

interface Isomorphism a b => Equivalence a b where
  toFrom : to << from = Builtins.id
  fromTo : from << to = Builtins.id
(<~>) : Type -> Type -> Type
a <~> b = Isomorphism a b

-- We should first talk about adjunctions before moving to isomorphisms
{-interface Isomorphism a b => Equivalence a b where
  toFrom : to << from = id
  fromTo : from << to = id-}

--interface Equivalence (a : t) (b : t) => Congruence a b where
  --cong : (f : t -> u) -> Equivalence (f a) (f b)
--https://github.com/jaredloomis/Idris-HoTT/blob/master/Main.idr

--Isomorphism (=) where
--  to   = ?rhs
--  from = ?rhs2
