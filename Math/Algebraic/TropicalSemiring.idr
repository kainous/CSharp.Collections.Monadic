

infixl 4 <>
infixl 5 +
infixl 6 *

interface Monoid ty where
  (<>) : ty -> ty -> ty
  id : ty

  associativity : a <> (b <> c) = (a <> b) <> c
  leftIdentity  : id <> a = a
  rightIdentity : a <> id = a

op : Monoid ty => ty -> ty -> ty
op = (<>)


--interface Monoid ty => CommutativeMonoid ty where
--  commutativity : a <> b = b <> a

--data

--interface Semiring ty where
--  (+) : ty -> ty -> ty
--  (*) : ty -> ty -> ty
--  zero : ty
--  one  : ty

--  additiveCommutativity : a + b = b + a

data Nat = Z | S Nat

interface SharedUnitSemiring ty where
  (+)   : ty -> ty -> ty
  (*)   : ty -> ty -> ty
  empty : ty

  additiveCommutativity : a + b = b + a
  additiveAssociativity : a + (b + c) = (a + b) + c

  leftAdditiveIdentity : empty + a = a
  rightAdditiveIdentity : a + empty = a

plus : Nat -> Nat -> Nat
plus    Z  y = y
plus (S x) y = S (plus x y)

SharedUnitSemiring Nat where
  (*) = plus
  a + Z = a
  Z + a = a
  (S a) + (S b) = S (a + b)



  --leftAdditiveIdentity = rightAdditiveIdentity
