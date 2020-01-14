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


data NaturalTransformation : (obj -> Type) -> (obj -> Type) -> Type where
  MkNaturalTransformation : (f : obj -> Type) -> (g : obj -> Type) -> NaturalTransformation f g

data NaturalComposition : (a -> Type) -> (a -> Type) -> (a -> Type) -> (a -> Type) -> Type where
  MkNaturalComposition : (f, f', g, g' : Type -> Type) -> NaturalComposition f f' g g'

-- Bring forward adjunctions
-- https://github.com/Risto-Stevcev/idris-functors/blob/master/Data/Functor/Compose.idr
-- https://github.com/TimRichter/CId/blob/0963f048311bacf5522bc24d4e9fba5c4b587dca/Category.lidr
-- http://www.stephendiehl.com/posts/adjunctions.html
vert :
  (Functor h, Functor f', Functor g, Functor g') =>
  NaturalTransformation f' g' ->
  NaturalTransformation f  g  ->
  NaturalComposition h f' g g'
vert (MkNaturalTransformation f' g') (MkNaturalTransformation f g) = ?vert_rhs_2

horiz :
  (Functor h, Functor f', Functor g, Functor g') =>
  NaturalTransformation f' g' ->
  NaturalTransformation f  g  ->
  NaturalComposition h f' g g'
horiz a b = MkNaturalComposition (map b (a x))

--laws : (a << b) `vert` (a' << b') = (a `horiz` a') << (b `horiz` b')
