module Math.Algebraic.Semigroup

import Builtins
import Math.Algebraic.Magma
import Math.Numeric.Nat

%default total
%access public export

||| This is NOT an implementation of BinNat, but something to make type compile
--data PosNat = One | PS BinNat

--fromInteger : Integer -> BinNat
--fromInteger x = One


--interface Magma ty => FlexibleMagma ty where




-- namespace this repeat in a way such that zero is useful for monoids
interface Magma ty => PowerAssociative' ty where
  repeat : (b : PosNat) -> ty -> ty

-- power associative implementation different if monoid than semigroup
interface PowerAssociative' ty => PowerAssociative ty where
  powerAssociativity : associator
  --repeatedMonoid : a <> a = repeat 2 a -- use iter
  repeatedMonoid : repeat 2 a = repeat 2 a

--interface Magma ty => Semigroup' ty where
  --||| Effectively, this equates to integral exponentiation whereas a <> a <> a can be specified as a ** 3 by calling repeat 3 a
  --||| it is because this may need to be overridden that the implementation
  --repeat : BinNat => b -> ty -> ty


--interface Semigroup' ty => Semigroup ty where
--  associativity : {a, b, c : ty} -> a <> (b <> c) = (a <> b) <> c
