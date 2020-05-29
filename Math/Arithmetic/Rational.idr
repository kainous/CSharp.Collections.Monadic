import Builtins

data Nat = Z | S Nat

plus : (x, y : Nat) -> Nat
plus x   Z   = x
plus x (S y) = S (x `plus` y)

data Comparison : (n, m : Nat) -> Type where
  EQ : Comparison x x
  LT : (y : Nat) -> Comparison x (x `plus` S y)
  GT : (x : Nat) -> Comparison (y `plus` S x) y

compare : (n, m : Nat) -> Comparison n m
compare Z Z = EQ
compare (S x) Z = GT _
compare Z (S x) = LT _
compare (S y) (S x) with (compare x y)
  compare x' y' | 

data LTE : (n, n : Nat) -> Type where
  LTEZero : LTE Z right
  LTESucc : LTE left right -> LTE (S left) (S right)

{-
GTE : Nat -> Nat -> Type
GTE = flip LTE

LT : Nat -> Nat -> Type
LT left = LTE (S left)

GT : Nat -> Nat -> Type
GT = flip LT -}

total
sub : (m, n : Nat) -> .{auto smaller : LTE n m} -> Nat
--sub x Z = x
--sub (S x) (S y) = x `sub` y
sub x Z = x
sub (S x) (S y) {smaller = (LTESucc _)} = sub x y


subIdent : (x : Nat) -> sub x Z = x
subIdent Z = ?subRight
subIdent (S x) = ?subIdent_rhs_2

data IsSucc : (n : Nat) -> Type where
  ItIsSucc : IsSucc (S n)

subLargerZero : IsSucc x -> IsSucc (x `sub` Z)
--subLargerZero x = IsSucc (sub x Z)

data Dec : Type -> Type where
  Yes : (prf : prop) -> Dec prop
  No  : (contra : Not prop) -> Dec prop

interface DecEq ty where
  total decEq : (x, y : ty) -> Dec (x = y)

DecEq Nat where
  decEq Z Z = Yes Refl
  decEq (S x) Z = ?sdofins
  decEq Z (S y) = ?rhsf_1
  decEq (S x) (S y) = ?rhsf_4

--LT : Nat -> Nat -> Type
--LT left right = LTE (S left) right


total
{-- ->  .{auto mNotZero : IsSucc m} -> .{auto nNotZero : IsSucc n} --}
gcd : (m, n : Nat) -> .{auto mNatZero : IsSucc m} -> Nat
--gcd x y =

--  case (compare x y) of
  --        EQ => x
    --      LT => gcd x (y `sub` x)
      --    GT => ?gcdr --gcd (x `sub` y) y


data Either a b
  = Left  a
  | Right b

data Sign ty
  = Pos ty
  | Zero
  | Neg ty

--data Int : Nat -> Nat -> Type where
--  I : (a : Nat) -> (b : Nat) -> Either (a = Z) (b = Z) -> Int a b
