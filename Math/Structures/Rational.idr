import Builtins

data Bool = T | F

infixl 8 /=

(/=) : (x : a) -> (y : a) -> Bool

data Nat = Z | S Nat

data PosRat
  = R1
  | Left  PosRat
  | Right PosRat

inv : PosRat -> PosRat
inv  R1       = R1
inv (Left x)  = Right (inv x)
inv (Right x) = Left  (inv x)

infixl 4 #

data Dec : Type -> Type where
  Yes : (prf : prop) -> Dec prop
  No  : (contra : Not prop) -> Dec prop

interface DecEq ty where
  decEq : (x, y : ty) -> Dec (x = y)

ZnotS : Z = S n -> Void
ZnotS Refl impossible

succInjective : (a, b : Nat) -> S a = S b -> a = b
succInjective _ _ Refl = Refl

negEqSym : .{a, b : ty} -> Not (a = b) -> Not (b = a)
negEqSym = (>>) sym

DecEq Nat where
  decEq Z Z = Yes Refl
  decEq Z (S _) = No ZnotS
  decEq (S _) Z = No (negEqSym ZnotS)
  decEq (S a) (S b) with (decEq a b)
    | Yes p = Yes <| cong p
    | No  p = No  <| \h : (S a = S b) => p <| succInjective a b h
{-
(#) : (n : Nat) -> (d : Nat) -> {auto prf : Not (s = 0)} -> {auto prf : Not (d = 0)} -> PosRat
x # y with (decEq x y)
  Yes _ = R1

(S Z) # (S Z)     = R1
(S Z) # (S (S Z)) = Right R1
(S (S Z)) # (S Z) = Left R1
(S (S Z)) # (S (S Z)) = R1
(S (S (S (S Z)))) # (S Z) = Left (Left R1)
--(S (S (S (S Z)))) # (S (S Z)) =



plus : PosRat -> PosRat -> PosRat
plus x R1        = ?plus_rhs_1
plus x (Left y)  = ?plus_rhs_2
plus x (Right y) = ?plus_rhs_3
-}
