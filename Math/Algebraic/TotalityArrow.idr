module Math.Algebraic.TotalityArrow

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid
import Math.Algebraic.Magma
import Math.Algebraic.Semigroup

%default total
%access public export

data MagmoidArrow : ty -> () -> () -> Type where
  MkMagmoidArrow : ty -> MagmoidArrow ty () ()

Magma ty => Magmoid (MagmoidArrow ty) where
  -- Isn't this some kind of map2 function? Does this mean that MagmoidArrow is a(n Applicative)Functor?
  compose (MkMagmoidArrow x) (MkMagmoidArrow y) = MkMagmoidArrow (x <> y)

Semigroup' ty => Semigroupoid (MagmoidArrow ty) where

  
