import Builtins

infixl 4 *
infixl 3 +
infixl 8 <=

data Either a b = Left a | Right b
data Bool = T | F

interface TotalOrder ty where
  (<=) : ty -> ty -> Bool

interface CommutativeSemiring ty where
  (+) : ty -> ty -> ty
  (*) : ty -> ty -> ty
  one  : ty
  zero : ty
  --neg : ty -> ty

  commutativePlus  : (a, b : ty) -> a + b = b + a
  commutativeTimes : (a, b : ty) -> a * b = b * a
  timesIdent : (a : ty) -> one  * a = a
  zeroIdent  : (a : ty) -> zero + a = a
  plusAssociative  : (a, b, c : ty) -> a + (b + c) = (a + b) + c
  timesAssociative : (a, b, c : ty) -> a * (b * c) = (a * b) * c
  --negInverse : (a : ty) -> a + neg a = zero
  prodDistribSum : (a, b, c : ty) -> a * (b + c) = a * b + a * c
  noZeroDivisors : {a, b : ty} -> a * b = 0 -> Either (a = 0) (b = 0)

--interface CommutativeRing ty => Natural ty where

interface CommutativeSemiring ty => CommutativeRing ty where
  neg : ty -> ty
  negInverse : (a : ty) -> a + neg a = zero

data Nat = Z | S Nat

plus : (a, b : Nat) -> Nat
plus a    Z  = a
plus a (S b) = S (a `plus` b)

rhs : (a : Nat) -> (b : Nat) -> S (plus a b) = plus (S b) a
rhs Z     Z  = Refl
rhs (S x) Z  = rewrite rhs x Z in Refl
rhs Z (S x)     = rewrite rhs Z x in ?rhs_rhs_1
rhs (S y) (S x) = ?rhs_rhs_3

isCommutative : (a, b : Nat) -> a `plus` b = b `plus` a
isCommutative a b = result a b where
  baseCase : (a : Nat) -> a = plus Z a
  baseCase    Z  = Refl
  baseCase (S x) = rewrite baseCase x in Refl

  result : (a, b : Nat) -> a `plus` b = b `plus` a
  result a Z = baseCase a
  result a (S b) = rhs a b


{-isCommutative a Z  = leftPlusIdent a where
  leftPlusIdent : (a : Nat) -> a = Z `plus` a
  leftPlusIdent Z = Refl
  leftPlusIdent (S x) = rewrite leftPlusIdent x in Refl
isCommutative Z x = ?isCommutative_rhs_3
isCommutative (S y) (S x) = case _ of
                                 case_val => ?isCommutative_rhs_4-}


CommutativeSemiring Nat where
  zero = Z
  one  = S Z
  a +   Z   = a
  a + (S b) = S (a + b)
  a *   Z   = Z
  a * (S b) = a + (a * b)
  commutativePlus Z     Z = Refl
  commutativePlus (S x) Z = ?rhs2
  commutativePlus a (S x) = ?rhs_2


--data Intgr = Pos (S Nat)
  --Pos  : S Nat
  --Zero : Intgr
  --Neg  : S Nat

  --= Pos (NonZeroNat | NotZero)
  --| Zero
  --| Neg NonZeroNat

{-
data Intgr
  = Pos (NonZeroNat | NotZero)
  | Zero
  | Neg NonZeroNat

natPlus : NonZeroNat -> NonZeroNat -> NonZeroNat
natPlus x  NZ1  = S x
natPlus x (S y) = S (x `natPlus` y)

natTimes : NonZeroNat -> NonZeroNat -> NonZeroNat
natTimes x  NZ1  = x
natTimes x (S y) = x `natPlus` (x `natTimes` y)

IntegralDomain Intgr where
  zero = Zero
  one  = Pos NZ1
  neg (Pos x) = Neg x
  neg   Zero  = Zero
  neg (Neg x) = Pos x

  Zero + y = y
  (Pos x) + (Pos y) = Pos (x `natPlus` y)
  (Pos x) +  Zero   = x
  (Pos x) + (Neg y) = ?rhs_5
  (Neg x) + y       = ?rhs_3
-}
