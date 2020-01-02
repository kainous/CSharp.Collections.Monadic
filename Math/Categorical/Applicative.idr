module Math.Categorical.Applicative

import Builtins
import Math.Categorical.Functor

%default total
%access public export
--infixl 4 <|, |>

interface Point (f : Type -> Type) where
  wrap : a -> f a
  extract : f a -> a

interface Applicable (f : Type -> Type) where
  ap : f (a -> b) -> f a -> f b

-- Somehow, we should also define dictionaries such that Applicable works here
-- (x |> dict) then gives us y. It would make for a Cartesian Closed Category with exponentiation

interface (Point f, Applicable f) => Applicative' (f : Type -> Type) where

Applicative' f => Functor' f where
  map f x = ap (wrap f) x

(<|) : Applicative' f => f (a -> b) -> f a -> f b
(<|) = ap

(|>) : Applicative' f => f a -> f (a -> b) -> f b
(|>) = flip ap
