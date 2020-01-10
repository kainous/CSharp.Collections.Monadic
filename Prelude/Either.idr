module Prelude.Either

import Builtins
import Math.Functorial.Bifunctor

%default total
%access public export

data Either a b
  = Left a
  | Right b

Bifunctor Either where
  bimap f g (Left x)  = Left  (f x)
  bimap f g (Right y) = Right (g y)
