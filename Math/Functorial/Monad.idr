module Math.Functorial.Monad

import Builtins
import Math.Topological.Pointed
import Math.Functorial.Applicable
import Math.Functorial.Functor
import Math.Functorial.ApplicativeFunctor

interface Bindable (w : Type -> Type) where
  bind : (a -> w b) -> w a -> w b

interface (Bindable w, RawApplicativeFunctor w) => RawMonad (w : Type -> Type) where
  merge : w (w a) -> w a
  merge = bind id

  Bindable w where
    bind f x = merge (map f x)

  Applicable w where
    ap f x = bind (\g => bind (wrap << g) x) f

  RawFunctor w where
    map = bind << (<<) wrap

data Identity x = Id x

Pointed Identity where
  wrap x = Id x

Bindable Identity where
  bind f (Id x) = f x

--RawMonad Identity where
--  merge x = ?rhs
