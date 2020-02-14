module Math.Numeric.Nat

import Builtins

%default total
%access public export

data Nat = Z | S Nat

data IsSucc : (n : Nat) -> Type where
  ItIsSucc : IsSucc (S n)

PosNat : Type
PosNat = DPair Nat IsSucc

plusNat : Nat -> Nat -> Nat
plusNat  Z y = y
plusNat (S x) y = S (plusNat x y)

multNat : Nat -> Nat -> Nat
multNat Z _ = Z
multNat (S n) m = plusNat n (multNat n m)

total
plus : PosNat -> PosNat -> PosNat
plus (S n ** _) (m ** _) = (plusNat (S n) m ** ItIsSucc)

total
mult : PosNat -> PosNat -> PosNat
mult (n ** pfn) (m ** pfm) =
  (multNat n m ** timesPos n m pfn pfm) where
  timesPos : (n, m : Nat) -> IsSucc n -> IsSucc m -> IsSucc (multNat n m)
  timesPos n@(S _) m@(S _) pfn pfm = ItIsSucc

---total
--mult : PosNat -> PosNat -> PosNat
--mult One y = y
--mult x One = x
--mult (PS x) y@(PS _) = x `plus` (x `mult` y)

-- Get some univalence involved in associating PosNat with Nat + 1

data I ty
  = Pos ty
  | Zero
  | Neg ty

Int : Type
Int = I PosNat

total
plusInt : I PosNat -> I PosNat -> I PosNat
plusInt Zero y = y
plusInt x Zero = x

--plusInt (Pos One) (Pos One) = Pos (PS One)
--plusInt (Neg One) (Neg One) = Neg (PS One)
--plusInt (Pos One) (Neg One) = Zero

--plusInt (Pos x) (Pos y) = Pos (plus x y)
--plusInt (Neg x) (Neg y) = Neg (plus x y)

--plusInt (Pos (PS x)) (Neg (PS y)) = plusInt (Pos x) (Neg y)
--plusInt (Neg (PS x)) (Pos (PS y)) = plusInt (Neg x) (Pos y)

{-multInt : I PosNat -> I PosNat -> I PosNat
multInt Zero y = Zero
multInt x Zero = Zero

multInt (Pos x) (Pos y) = Pos (x `mult` y)
multInt (Pos x) (Neg y) = Neg (x `mult` y)
multInt (Neg x) (Neg y) = Pos (x `mult` y)

data SternBrocotRational = L SternBrocotRational | R SternBrocotRational

inv : I SternBrocotRational -> I SternBrocotRational
inv (Pos x) = ?inv_rhs_1
inv Zero = ?inv_rhs_2
inv (Neg x) = ?inv_rhs_3

-}


--data Nat = Z | S Nat

--data PosNat
