module Math.Categorical.Isomorphism

import Math.Categorical.HomSet
import Math.Categorical.Semigroupoid

%default total
%access public export

interface Isomorphism a b where
  constructor MkIso
  to   : a ~> b
  from : b ~> a
  toFrom : to << from = id
  fromTo : from << to = id
