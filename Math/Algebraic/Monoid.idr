--module Math.

infixl 4 <>

data Optional a = OneOf a | None

interface Semigroup' ty where
  (<>) : ty -> ty -> ty

interface Semigroup' ty => Monoid' ty where
  neutral : ty

data AdjoinUnit m = MkAdjoinUnit (Optional m)

AdjoinUnitEx : (m : Type) -> Type
AdjoinUnitEx x = Optional x

AdjoinAbsorbEx : (m : Type) -> Type
AdjoinAbsorbEx x = Optional x

data B = T | F
Semigroup' B where
  T <> b = b
  F <> _ = F

test0 : AdjoinUnitEx B
test0 = OneOf T

test1 : AdjoinAbsorbEx B
test1 = OneOf T

interface Monoid' ty => MonoidWithZero' ty where
  absorb : ty

Semigroup' ty => Semigroup' (AdjoinUnitEx ty) where
  (OneOf x) <> (OneOf y) = OneOf (x <> y)
  a <> None = a
  None <> b = b

--Semigroup' ty => Semigroup' (AdjoinAbsorbEx ty) where
--  a <> b = ?rhs

Semigroup' ty => Monoid' (AdjoinUnitEx ty) where
  neutral = None

Semigroup' ty => Semigroup' (AdjoinUnit ty) where
  a <> (MkAdjoinUnit None) = a
  (MkAdjoinUnit None) <> b = b
  (MkAdjoinUnit (OneOf y)) <> (MkAdjoinUnit (OneOf x)) = MkAdjoinUnit (OneOf (x <> y))

Semigroup' ty => Monoid' (AdjoinUnit ty) where
  neutral = MkAdjoinUnit None
