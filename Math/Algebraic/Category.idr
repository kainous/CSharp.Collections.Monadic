module Math.Algebraic.Category

%access public export
%default total



interface Category (mor : obj -> obj -> Type) where
  id : mor a a
  comp : mor b c -> mor a b -> mor a c

interface (Category r, Category t) => PFunctor p r t | p r -> t, p t -> r where


--interface Category mor => CartesianMonoidalCategory (mor : obj -> obj -> Type) where
--  prod :

--interface CartesianMonoidalCategory mor => CartesianClosedCategory (mor : obj -> obj -> Type) where
--  eval : (mor z y)

  -- partial applicatino ap :
