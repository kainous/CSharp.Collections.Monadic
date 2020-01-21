module Prelude.Lazy

import Builtins
import Math.Functorial.Functor

%default total
%access public export

data DelayReason = Infinite | LazyValue

data Delayed : DelayReason -> Type -> Type where
  ||| Delayed computation
  Delay : {t, a : _} -> (val : a) -> Delayed t a

force : {t, a : _} -> Delayed t a -> a
force (Delay x) = x

-- These are monadic
%error_reverse
Lazy : Type -> Type
Lazy t = Delayed LazyValue t

%error_reverse
Inf  : Type -> Type
Inf t = Delayed Infinite t

RawFunctor (Delayed LazyValue) where
  map f (Delay val) = Delay (f val)

Functor (Delayed LazyValue) where
  preservesIdentity    (Delay val) = Refl
  preservesComposition (Delay val) = Refl

RawFunctor (Delayed Infinite) where
  map f (Delay val) = Delay (f val)

Functor (Delayed Infinite) where
  preservesIdentity    (Delay val) = Refl
  preservesComposition (Delay val) = Refl
