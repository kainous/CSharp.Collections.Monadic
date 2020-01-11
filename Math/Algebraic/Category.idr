module Math.Algebraic.Category

import Builtins

%access public export
%default total



interface Category (mor : obj -> obj -> Type) where
  id : mor a a
  comp : mor b c -> mor a b -> mor a c

--interface (Category r, Category t) => PFunctor p r t | p r -> t, p t -> r where


--interface Category mor => CartesianMonoidalCategory (mor : obj -> obj -> Type) where
--  prod :

--interface CartesianMonoidalCategory mor => CartesianClosedCategory (mor : obj -> obj -> Type) where
--  eval : (mor z y)

  -- partial applicatino ap :



interface Equivalence a b where
  to : a -> b
  from : b -> a
  tofrom : to >> from = id
  fromto : from >> to = id

CategoricalCommutator : Category mor => (f : mor a b) -> (g : mor b c) -> Equivalence (mor a c) (mor a c) -> Type
CategoricalCommutator f g x = ?CategoricalCommutator_rhs
