module Math.Algebraic.Semigroup

import Builtins
import Math.Algebraic.Magma

%default total
%access public export

interface Magma ty => Semigroup' ty where
  ||| Effectively, this equates to integral exponentiation whereas a <> a <> a can be specified as a ** 3 by calling repeat 3 a
  ||| it is because this may need to be overridden that the implementation
  repeat : BinNat => b -> ty -> ty


interface Semigroup' ty => Semigroup ty where
  associativity : {a, b, c : ty} -> a <> (b <> c) = (a <> b) <> c
