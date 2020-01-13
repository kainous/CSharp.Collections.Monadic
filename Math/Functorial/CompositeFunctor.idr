module Math.Functorial.CompositeFunctor

import Builtins
import Math.Topological.Pointed
import Math.Functorial.Applicable
import Math.Functorial.ApplicativeFunctor
import Math.Functorial.Functor

%default total
%access public export

--CompositeFunctor : (f : Type -> Type) -> (g : Type -> Type) -> (x:Type) -> Type
--CompositeFunctor f g x = f (g x)

data CompositeFunctor : (f:Type -> Type) -> (g:Type -> Type) -> (x:Type) -> Type where
  MkCompositeFunctor : f (g x) -> CompositeFunctor f g x

(RawFunctor f, RawFunctor g) => RawFunctor (CompositeFunctor f g) where
  map h (MkCompositeFunctor x) = MkCompositeFunctor (map h <! x)

(Pointed f, Pointed g) => Pointed (CompositeFunctor f g) where
  wrap = MkCompositeFunctor << wrap << wrap

(ApplicativeFunctor f, Applicable g) => Applicable (CompositeFunctor f g) where
  ap (MkCompositeFunctor h) (MkCompositeFunctor x) = x |> map ap h |> MkCompositeFunctor
