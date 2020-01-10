module Math.Functorial.Bifunctor

import Builtins

%default total
%access public export

namespace Functorial
  interface Bifunctor (p : Type -> Type -> Type) where
    bimap : (a -> b) -> (c -> d) -> p a c -> p b d
    bimap f g = first f << second g

    first : (a -> b) -> p a c -> p b c
    first = flip bimap id

    second : (b -> c) -> p a b -> p a c
    second = bimap id

  Bifunctor Pair where
    bimap f g (x, y) = (f x, g y) -- (f a, f b)
