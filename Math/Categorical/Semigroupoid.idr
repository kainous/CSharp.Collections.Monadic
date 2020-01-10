module Math.Categorical.Semigroupoid

import Builtins
import Math.Categorical.Magmoid

%default total
%access public export

namespace Categorical

  -- This is the unverified
  interface Magmoid mor => RawSemigroupoid (mor : obj -> obj -> Type) where

  (<<) : RawSemigroupoid mor => mor b c -> mor a b -> mor a c
  (<<) = flip compose

  (>>) : RawSemigroupoid mor => mor a b -> mor b c -> mor a c
  (>>) = compose

  -- This is verfied for associativity
  interface RawSemigroupoid mor => Semigroupoid (mor : obj -> obj -> Type) where
    compositionIsAssociative : {f : mor c d} -> {g : mor b c} -> {h : mor a b} -> f << (g << h) = (f << g) << h
