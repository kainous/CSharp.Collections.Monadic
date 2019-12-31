module Math.Categorical.Semigroupoid

import Builtins
import Math.Categorical.Magmoid

%default total

%access public export

-- This is the unverified
interface Magmoid mor => Semigroupoid' (mor : obj -> obj -> Type) where

(<<) : Semigroupoid' mor => mor b c -> mor a b -> mor a c
(<<) = compose

(>>) : Semigroupoid' mor => mor a b -> mor b c -> mor a c
(>>) = flip compose

-- This is verfied for associativity
interface Semigroupoid' mor => Semigroupoid (mor : obj -> obj -> Type) where
  compositionIsAssociative : {f : mor c d} -> {g : mor b c} -> {h : mor a b} -> f << (g << h) = (f << g) << h
