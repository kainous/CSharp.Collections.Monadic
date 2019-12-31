import Builtins



data Nat = Z | S Nat

plus : Nat -> Nat -> Nat
plus x    Z  = x
plus x (S y) = S (x `plus` y)

mult : Nat -> Nat -> Nat
mult x    Z  = Z
mult x (S y) = y `plus` (x `mult` y)

fact : Nat -> Nat
fact    Z =  S Z
fact (S x) = (S x) `mult` (fact x)

factDict : (n : Nat ** fact n)
factDict = (n ** fact n)
