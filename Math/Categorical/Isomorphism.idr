module Math.Categorical.Isomorphism

import Math.Categorical.HomSet
import Math.Categorical.Semigroupoid

%default total
%access public export

interface Isomorphism a b where
  constructor MkIso
  to   : a ~> b
  from : b ~> a

interface Isomorphism a b => Equivalence a b where
  toFrom : to << from = id
  fromTo : from << to = id

interface Equivalence a b => Congruence a b where

--https://github.com/jaredloomis/Idris-HoTT/blob/master/Main.idr
