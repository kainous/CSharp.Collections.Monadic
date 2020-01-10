module Math.Functorial.Applicable

import Builtins

%default total
%access public export

interface Applicable (f : Type -> Type) where
  ap : f (a -> b) -> f a -> f b

(<|) : Applicable f => f (a -> b) -> f a -> f b
(<|) = ap

(|>) : Applicable f => f a -> f (a -> b) -> f b
(|>) = flip ap
