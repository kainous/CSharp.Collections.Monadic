import Builtins

%default total
%access public export

interface Magma ty where
  op : ty -> ty -> ty

infixl 4 <>

(<>) : Magma ty => ty -> ty -> ty
(<>) = op

interface Magma ty => Semigroup ty where
  associative : (x, y, z : ty) -> x <> (y <> z) = (x <> y) <> z

interface Semigroup ty => Monoid ty where
  ident : ty

  leftIdent  : (x : ty) -> x <> ident = x
  rightIdent : (x : ty) -> ident <> x = x

interface Monoid ty => CommutativeMonoid ty where
  commutative : (x, y : ty) -> x <> y = y <> x

interface Monoid ty => Group ty where
  inverse : ty -> ty

  leftInverse  : (x : ty) -> inverse x <> x = ident
  rightInverse : (x : ty) -> x <> inverse x = ident

interface (CommutativeMonoid ty, Group ty) => CommutativeGroup ty where

interface Semiring ty where
  sum  : CommutativeGroup ty
  prod : Monoid ty

data Bool = T | F

[SumMagma] Magma Bool where
  op T _ = T
  op F y = y

[SumMonoid] Semigroup Bool where
  a <+> b = ?holeSemigroup

--Semiring Bool where
