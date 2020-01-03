module Math.Algebraic.Magma

import Builtins

%default total
%access public export

mytheorem : {f : (a -> b) -> c} -> f = (\g => f (\x => g x))
mytheorem = funext <| \_ => Refl

associativityOfFunctions : {f : (a -> b)} -> {g : (b -> c)} -> {h : (c -> d)} -> f >> (g >> h) = (f >> g) >> h
associativityOfFunctions = funext <| \_ => Refl

infixl 2 <>

interface Magma ty where
  op : ty -> ty -> ty

--Dual 

--equivariantMappings : f >> g = g >> f
--equivariantMappings = ?equivariantMappings_rhs

data BinaryOp ty
  = Op (ty -> ty -> ty)
  | DualOp (ty -> ty -> ty)

Dual : BinaryOp ty -> BinaryOp ty
Dual (Op f) = DualOp f
Dual (DualOp f) = Op f

interface Pointed ty where
  Point : ty

infixl 2 <>

interface Magma ty where
  op : BinaryOp ty

--DualMagma : Magma ty -> Magma ty
--DualMagma m = op ?sd

(<>) : Magma ty => ty -> ty -> ty
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
