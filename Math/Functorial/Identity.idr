module Math.Functorial.Identity

import Builtins
import Math.Topological.Pointed
import Math.Functorial.Functor
import Math.Functorial.Applicable
import Math.Functorial.ApplicativeFunctor

%default total
%access public export

data Identity x = Id x

Pointed Identity where
  wrap = Id

RawFunctor Identity where
  map f (Id x) = Id (f x)

Functor Identity where
  preservesComposition (Id x) = Refl
  preservesIdentity    (Id x) = Refl

Applicable Identity where
  ap f x = ?rhs

RawApplicativeFunctor where
