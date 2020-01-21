module Math.Functorial.Bindable

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid

%default total
%access public export

-- Should we even have >=> or just use >> and <<    ???
infixl 4 >>=, =<<, >=>, <=<

data Object a = Obj a

interface Bindable (f : Type -> Type) where
  bind : (a -> f b) -> f a -> f b

(=<<) : Bindable f => (a -> f b) -> f a -> f b
(=<<) = bind

(>>=) : Bindable f => f a -> (a -> f b) -> f b
(>>=) = flip bind

-- Should this be a category with >> and <<
(>=>) : Bindable m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \x => f x >>= g

(<=<) : Bindable m => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) = flip (>=>)

--Magmoid (Bind) where
record KleisiMorphism (m : Type -> Type) a b where
  constructor Kleisi
  applyKleisi : a -> m b

Bindable m => Magmoid (KleisiMorphism m) where
  compose (Kleisi f) (Kleisi g) = Kleisi (\x => f x >>= g)

Bindable m => Semigroupoid (KleisiMorphism m) where
