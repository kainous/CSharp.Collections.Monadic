module Prelude.Lazy

%default total
%access public export

data DelayReason = Infinite | LazyValue

data Delayed : DelayReason -> Type -> Type where
  ||| Delayed computation
  Delay : {t, a : _} -> (val : a) -> Delayed t a

Force : {t, a : _} -> Delayed t a -> a
Force (Delay x) = x

-- These are monadic
%error_reverse
Lazy : Type -> Type
Lazy t = Delayed LazyValue t

%error_reverse
Inf  : Type -> Type
Inf t = Delayed Infinite t
