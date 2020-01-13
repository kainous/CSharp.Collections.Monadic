module Math.Functorial.Monad

import Builtins
import Math.Topological.Pointed
import Math.Functorial.Applicable
import Math.Functorial.Functor
import Math.Functorial.ApplicativeFunctor

interface Bindable (w : Type -> Type) where
  bind : (a -> w b) -> w a -> w b

interface (Bindable w, RawApplicativeFunctor w) => Monad (w : Type -> Type) where
  merge : w (w a) -> w a
  merge = bind id

  Bindable w where
    bind f = map f >> join

  Applicable w where
    ap f x = bind f (\g => bind (wrap g) x)

  RawFunctor w where
    map f = f >> wrap |> bind
