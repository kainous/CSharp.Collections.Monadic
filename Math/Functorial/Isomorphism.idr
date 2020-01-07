module Math.Functorial.Isomorphism

import Builtins

%default total
%access public export


infixr 4 ~>, >>>, >>>>
||| HomSet
public export
data Morphism : Type -> Type -> Type where
  Mor : (a -> b) -> Morphism a b

--public export
--data Endomorphism : Type -> Type where
--  Endo : (a -> a) -> Endomorphism a

public export
(~>) : Type -> Type -> Type
(~>) = Morphism

interface Isomorphism a b where
  to   : a ~> b
  from : b ~> a

interface Isomorphism a b => Equivalence a b where
  tofrom : to >> from = id
  fromto : from >> to = id
