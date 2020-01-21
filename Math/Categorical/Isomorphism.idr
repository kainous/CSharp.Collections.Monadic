module Math.Categorical.Isomorphism

import Builtins
import Math.Functorial.Functor
import Math.Categorical.Morphism
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid

%default total
%access public export

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

interface Equivalence a b => Congruence a b where
  cong : (f : t -> u) -> Equivalence (f a) (f b)
--https://github.com/jaredloomis/Idris-HoTT/blob/master/Main.idr

Isomorphism (=) where
  to   = ?rhs
  from = ?rhs2
