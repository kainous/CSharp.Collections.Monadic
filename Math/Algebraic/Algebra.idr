cong : {f : t -> u} -> (a = b) -> (f a = f b)
cong Refl = Refl

data Equation ty = Eq ty ty

data AlgebraicExpression : ty -> Type where
  Add : (AlgebraicExpression ty) -> (AlgebraicExpression ty) -> AlgebraicExpression ty
  Mul : (AlgebraicExpression ty) -> (AlgebraicExpression ty) -> AlgebraicExpression ty
  Neg : (AlgebraicExpression ty) -> (AlgebraicExpression ty)
  Inv : (AlgebraicExpression ty) -> (AlgebraicExpression ty) -- How to deal with non-zero?
  Embed : ty -> AlgebraicExpression ty

-- This is better done as a total function with proof and non-proof
partial
extract : AlgebraicExpression ty -> ty
extract (Embed x) = x

-- comonoidal
--eval : AlgebraicExpression ty -> ty
--eval (Add x y) = eval x + eval y
--eval (Mul x y) = eval x * eval y
--eval (Neg x) = neg (eval x)
--eval (Inv x) = inv (eval x)
--eval (Embed x) = x

normalize : AlgebraicExpression ty -> AlgebraicExpression ty
normalize (Add x y) = ?normalize_rhs_1
normalize (Mul x y) = ?normalize_rhs_2
normalize (Neg x) = ?normalize_rhs_3
normalize (Inv x) = ?normalize_rhs_4
normalize (Embed x) = ?normalize_rhs_5

test0 : normalize (x `Add` x) = normalize ((Embed 2) `Mul` x)
test0 = ?test0_rhs

-- Prove that (x + x) = 2 * x

-- How to promote this to equations with unknowns, at the type level?
