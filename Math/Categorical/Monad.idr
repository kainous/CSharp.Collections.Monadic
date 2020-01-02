module Math.Categorical.Monad

import Builtins
import Math.Categorical.Functor
import Math.Categorical.Applicative
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid

%default total
%access public export

interface Bind (f : Type -> Type) where
  bind : (a -> f b) -> f a -> f b

  --- Does this form a semigroupoid? no, but Applicative does

infixl 1 =<<, >>=

(=<<) : Bind f => (a -> f b) -> f a -> f b
(=<<) = bind

(>>=) : Bind f => f a -> (a -> f b) -> f b
(>>=) = flip bind

-- Do we need applicative??? is Pointed enough?
interface (Bind f, Applicative' f) => Monad' (f : Type -> Type) where

-- This is typically called "join", and this REALLY needs to be an alternative definition for monad
  fuse : Monad' f => f (f a) -> f a
  fuse x = x >>= id
  -- fuse << map fuse = fuse << fuse
  -- fuse << (map (map f)) = map f << fuse
  -- fuse << map (wrap) = fuse << wrap = id

  --We cannot do this, because Idris doesn't allow us to define bind according to fuse
  --bind f ma = join (map f ma)

--interface Comonad (w : Type -> Type) where
--  extract : w a -> a
--  extend  : (w a -> b) -> w a -> w b

Bind m => Magmoid (KleisiMorphism m) where
  compose (Kleisi f) (Kleisi g) = Kleisi (\x => g x >>= f)

infixl 4 >=>

(>=>) : Bind m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \x => f x >>= g
