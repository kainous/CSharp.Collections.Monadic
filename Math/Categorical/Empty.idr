module Math.Categorical.Empty

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid
import Math.Categorical.Category

%default total
%access public export

data EmptyMorphism : (a, b : Void) -> Type where


--Magmoid (EmptyMorphism) where
--  compose = \_, a => absurd a
