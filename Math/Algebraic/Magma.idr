module Math.Algebraic.Magma

import Builtins

%default total
%access public export

mytheorem : {f : (a -> b) -> c} -> f = (\g => f (\x => g x))
mytheorem = funext <| \_ => Refl

associativityOfFunctions : .{f : (a -> b)} -> .{g : (b -> c)} -> .{h : (c -> d)} -> f >> (g >> h) = (f >> g) >> h
associativityOfFunctions = funext <| \_ => Refl

interface TernaryMagma ty where
  constructor MkTernaryMagma
  op3 : ty -> ty -> ty -> ty

interface TernaryMagma ty => Groud ty where
  biunit : ty
  -- only 2 associativities and transivity is necessary to prove the 3rd
  paraAssociativity1 : {a, b, c, d, e : ty} -> op3 (op3 a b c) d e = op3 a (op3 b c d) e
  paraAssociativity2 : {a, b, c, d, e : ty} -> op3 a (op3 b c d) e = op3 a b (op3 c d e)
  paraAssociativity3 : {a, b, c, d, e : ty} -> op3 a b (op3 c d e) = op3 (op3 a b c) d e

  leftBiunitary  : {k : ty} -> k = op3 h h k
  rightBiunitary : {k : ty} -> k = op3 k h h

  -- Grouds can be used to express/derive Relation Algebra

interface Magma ty where
  constructor MkMagma
  op2 : ty -> ty -> ty

-- can't use infix until Semigroup???
infixl 2 <>
(<>) : Magma ty => ty -> ty -> ty
(<>) = op2
--<L>

associator : Magma ty => (a, b, c : ty) -> (ty, ty)
associator a b c = (a <> (b <> c), (a <> b) <> c)

commutator : Magma ty => (a, b : ty) -> (ty, ty)
commutator a b = (a <> b, b <> a)

data Opposite : ty -> Type where
  MkOpposite : (f : ty -> ty -> ty) -> Opposite ty

--Magma ty => Magma ty where
--  op = MkOpposite(flip op)

--Dual : Magma ty -> Magma ty
--Dual m = prove m where
--  prove : Magma ty -> Magma ty
--  prove (MkMagma f) = MkMagma (flip f)

--dualOfDual : (m : Magma ty) -> Dual (Dual m) = m
--dualOfDual (MkMagma f) = cong flipOfFlipAp where
--  flipOfFlipAp : flip (flip f) = f
--  flipOfFlipAp = funext2 (\x, y => Refl)

--equivariantMappings : f >> g = g >> f
--equivariantMappings = ?equivariantMappings_rhs

interface Pointed ty where
  Point : ty

interface Magma ty => CommutativeMagma ty where
  commutativity : {a, b : ty} -> a <> b = b <> a

interface Magma ty => FlexibleMagma ty where
  flexibility : {a, b : ty} -> a <> (b <> a) = (a <> b) <> a

interface CommutativeMagma ty => JordanAlgebra ty where
  jordanIdentity : {x, y : ty} -> (x <> y) <> (x <> x) = x <> (y <> (x <> x))
  -- it should be noted that 5th powers of Jordan Algebras are well defined concepts. Can this be used?

--interface LeftAlternative --needs new word since Alternative Functor has different meaning

interface Magma ty => MedialMagma ty where
  mediality : {a, b, c, d : ty} -> (a <> b) <> (c <> d) = (a <> c) <> (b <> d)
  -- By itself, this is more of a generalization of commutativity than of associativity
  -- however, it should be noted that mediality has a categorical interpretation
     -- being a magma homomorphism from M * M to M
     -- see auto magma objects and generalizations to entropic algebras

-- Is this a poor name?
interface Magma ty => CompositionAlgebra ty where
  conj : ty -> ty
  norm : ty -> ty
  norm x = x <> conj x

  -- matrices are CompositionAlgebras
  -- is Linear Logic a Composition Algebra?
  -- Is the Stern Brocot tree a composition algebra using L and R as division?

  --inv : ty -> ty
  --inv x = conj x / norm x

  --bilinear : ty -> ty -> ty
  --bilinear x y = (norm (x + y) - norm x - norm y) / 2

-- this makes it power associative too, and gives it the general law : (repeat m x <> y) <> repeat n x = repeat m x <> (y <> repeat n x)

--dualOfCommutativeMagma : (m : CommutativeMagma ty) -> Dual m = m


--interface Magma ty where
--  op : BinaryOp ty

--DualMagma : Magma ty -> Magma ty
--DualMagma m = op ?sd

--(<>) {Op f} x y = f x y
--(<>) {DualOp f} x y = f x y
--(<>) x y = case op of
           --Op f => ?op_rhs
          -- DualOp f => ?op_rhs

--interface (Magma ty, Pointed ty) => LeftUnitalMagma ty where
--  leftUnitalMagma : point <> a = a

--interface (Magma ty, Pointed ty) => RightUnitalMagma ty where
--  rightUnitalMagma : a <> point = a

--interface (LeftUnitalMagma ty, RightUnitalMagma ty) where


--interface Magma ty => Semigroup ty where
--  associativity : a <> (b <> c) = (a <> b) <> c

--interface CommutativeMonoid ty => Magma ty where
--  commutativity : Dual op = op
