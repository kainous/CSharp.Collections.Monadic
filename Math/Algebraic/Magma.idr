module Math.Algebraic.Magma

import Builtins

%default total
%access public export

mytheorem : {f : (a -> b) -> c} -> f = (\g => f (\x => g x))
mytheorem = funext <| \_ => Refl

associativityOfFunctions : .{f : (a -> b)} -> .{g : (b -> c)} -> .{h : (c -> d)} -> f >> (g >> h) = (f >> g) >> h
associativityOfFunctions = funext <| \_ => Refl

interface Magma ty where
  constructor MkMagma
  op : ty -> ty -> ty

infixl 2 <>
(<>) : Magma ty => ty -> ty -> ty
(<>) = op

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
