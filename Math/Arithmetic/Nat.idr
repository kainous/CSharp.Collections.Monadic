import Builtins
--import Math.Structures.HomSet

infixl 3 +
infixr 4 *

data Nat = Z | S Nat

hyper : Nat -> Nat -> Nat -> Nat
hyper Z     a b = S b
hyper (S Z) a Z = a
hyper (S (S Z)) a Z = Z
hyper n a Z = S Z
hyper (S pn) a (S pb) = hyper pn a (hyper (S pn) a pb)
--fromInteger : Integer -> Nat
--fromInteger 0 = Z
--fromInteger n = S (n - 1)

--data Bin : Nat -> Type where
--  N : Bin 0
--O : .{n : Nat} -> Bin n -> Bin (0 + 2 * n)
--I : .{n : Nat} -> Bin n -> Bin (1 + 2 * n)

--iter : (n : Nat) -> (a -> a)
