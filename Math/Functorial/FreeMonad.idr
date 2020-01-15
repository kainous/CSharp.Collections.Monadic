module Math.Functorial.FreeMonad

import Builtins
import Math.Topological.Pointed
import Math.Functorial.Applicable
import Math.Functorial.Functor
import Math.Functorial.Bindable
import Math.Functorial.Monad

%default total
%access public export

-- The Free Monad is like an AST for using the properties of a Monad
-- It's also like a List type in a way
data Free : (f : Type -> Type) -> a -> Type where
  Pure : a -> Free f a
  Bind : f (Free f a) -> Free f a

RawFunctor f => RawFunctor (Free f) where
  map f (Pure x) = Pure (f x)
  map f (Bind x) = Bind (map (map f) x)

RawFunctor f => Pointed (Free f) where
  wrap = Pure

RawFunctor w => Applicable (Free w) where
  ap (Pure f) x = map f x
  ap (Bind f) x = Bind ((x |>) <! f)

RawFunctor w => Bindable (Free w) where
  bind f (Pure x) = f x
  bind f (Bind x) = Bind (map (bind f) x)

RawFunctor w => RawMonad (Free w) where

hoistFree : Functor g => ({a : Type} -> f a -> g a) -> Free f b -> Free g b
hoistFree _ (Pure x) = Pure x
hoistFree f (Bind x) = Bind (hoistFree f <! f x)

interface MonadFree (m : Type -> Type) (f : Type -> Type) | m where
  encase : f (m a) -> m a

MonadFree (Free f) f where
  encase = Bind

--  ap (Bind f) x = Bind (map f ?rhs)
    --Pure f' => Pure (f' x)
    --Bind f' => Bind (map (f' <! x))
