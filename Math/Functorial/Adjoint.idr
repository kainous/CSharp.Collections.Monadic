module Math.Functorial.Adjoint

import Builtins
import Math.Functorial.Functor
import Math.Categorical.Morphism

%default total
%access public export

interface (Functor f, Functor g) => Adjoint (f : Type -> Type) (g : Type -> Type) where
  unit   : a -> g (f a)
  counit : f (g a) -> a

Adjoint (Pair s) (Morphism s) where
  unit x = Mor (\s => (s, x))
  counit (s, Mor f) = f s

--data Comp : f -> g -> a -> Type where
  --MkComp : (Functor f)
