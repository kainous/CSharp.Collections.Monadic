module Math.Functorial.Adjoint

import Builtins
import Math.Functorial.Functor2
--import Math.Categorical.Morphism


%default total
%access public export

data (~>) a b = Mor (a -> b)

interface RawThinFunctor (f : Type -> Type) where
  map : (a -> b) -> (f a -> f b)  

Math.Functorial.Adjoint.RawThinFunctor ((~>) s) where
  map f (Mor g) = Mor (\x => f (g x))


Math.Functorial.Adjoint.RawThinFunctor (Pair s) where
  map f (x, y) = (x, f y)

interface (Math.Functorial.Adjoint.RawThinFunctor f, Math.Functorial.Adjoint.RawThinFunctor g) => Adjunction (f : Type -> Type) (g : Type -> Type) where
  unit   : a -> g (f a)
  counit : f (g a) -> a

Adjunction (Pair s) ((~>) s) where
  unit x = Mor (\s => (s, x))
  counit (s, Mor f) = f s

infixl 4 >>=

interface (Math.Functorial.Adjoint.RawThinFunctor f, Math.Functorial.Adjoint.RawThinFunctor g, Adjunction f g) => Monad (f : Type -> Type) (g : Type -> Type) where
  mu : g (f (g (f a))) -> g (f a)
  (>>=) : g (f a) -> (a -> g (f b)) -> g (f b)

  mu = map counit
  x >>= f = mu (map (map f) x)



--data Comp : f -> g -> a -> Type where
  --MkComp : (Functor f)
