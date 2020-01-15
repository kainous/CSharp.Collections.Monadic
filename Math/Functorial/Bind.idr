module Math.Functorial.Bind

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid

%default total
%access public export

-- Should we even have >=> or just use >> and <<    ???
infixl 4 >>=, =<<, >=>, <=<

data Object a = Obj a

interface Bind (f : Type -> Type) where
  bind : (a -> f b) -> f a -> f b

(=<<) : Bind f => (a -> f b) -> f a -> f b
(=<<) = bind

(>>=) : Bind f => f a -> (a -> f b) -> f b
(>>=) = flip bind

-- Should this be a category with >> and <<
(>=>) : Bind m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \x => f x >>= g

(<=<) : Bind m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) = flip (>=>)

--Magmoid (Bind) where
record KleisiMorphism (m : Type -> Type) a b where
  constructor Kleisi
  applyKleisi : a -> m b

Bind m => Magmoid (KleisiMorphism m) where
  compose (Kleisi f) (Kleisi g) = Kleisi (\x => f x >>= g)

Bind m => Semigroupoid (KleisiMorphism m) where
