module Math.Algebraic.Involutive

import Builtins

--interface Involutive ty where
--  op1 : ty ->

interface TernaryMagma ty where
  op3 : ty -> ty -> ty -> ty

infixl 4 +, -, *
interface Ring ty where
  Zero : ty
  One  : ty
  (+)  : ty -> ty -> ty
  (*)  : ty -> ty -> ty
  (-)  : ty -> ty -> ty

ringAssociator : Ring ty => ty -> ty -> ty -> ty
ringAssociator a b c = (a * b) * c - a * (b * c)

ringAntiassociator : Ring ty => ty -> ty -> ty -> ty
ringAntiassociator a b c = (a * b) * c + a * (b * c)

ringCommutator : Ring ty => ty -> ty -> ty
ringCommutator a b = a * b - b * a

ringAnticommutator : Ring ty => ty -> ty -> ty
ringAnticommutator a b = a * b + b * a

interface Ring ty => CommutativeRing ty where
  --commutativityOfMultiplicaton : ringCommutator a b = Zero

data RingCommutator ty = MkRingCommutator (Ring ty)

-- This should be a CommutativeGroup
{-RingCommutator ty => CommutativeRing ty where
  Zero = Zero
  One = One -- This fails, as there is no

  a + b = a + b
  a * b = a * b - b * a -}

--[RingAssociator] Ring ty => TernaryMagma ty where
--  op3 = ringAssociator

--[RingCommutator] Ring ty => CommutativeRing ty where

-- So we have Types
-- and Types that make Types

--using (ty : Type, o : ty)
data UnaryOperator ty = Op1 (ty -> ty)

data BinaryOperator = Op2 (ty -> ty -> ty)
data TernaryOperator = Op3 (ty -> ty -> ty -> ty)

-- Maybe properly named GraphObject???
-- This is more restrictive than (UnaryOperator Type)
data MorphismOfGraphs : ty -> Type where
  MorOG : ty -> MorphismOfGraphs ty

data B = T | F

data Maybe ty = Some ty | None

test23 : UnaryOperator Type
test23 = Op1 (Maybe)

data BimorphismOfGraphs : obj -> obj -> Type where
  BiMoG : a -> b -> BimorphismOfGraphs a b

--test0 : MorphismOfGraphs Type
--test0 = ?test0_rhs


-- Left-Cancellative
record Monomorphism where
  constructor MkMonomorphism
  Morph : b -> c
  Proof : {g1, g2 : a -> b} -> g1 >> Morph = g2 >> Morph -> g1 = g2

record Injective where
  constructor MkInjective
  InFunc : a -> b
  InProof1 : {x, y : a} -> InFunc x = InFunc y -> x = y
  InProof2 : {g1, g2 : b -> c} -> InFunc >> g1 = InFunc >> g2
  InProof3 : {InFunc' : b -> a} -> InFunc >> InFunc' = Builtins.id

record Epimorphism where
  EMorph : a -> b
  EProof : {g1, g2 : b -> c} -> EMorph >> g1 = EMorph >> g2 -> g1 = g2
