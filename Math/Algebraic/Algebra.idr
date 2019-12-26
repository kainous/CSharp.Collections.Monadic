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
eval : AlgebraicExpression ty -> ty
eval (Add x y) = eval x + eval y
eval (Mul x y) = eval x * eval y
eval (Neg x) = neg (eval x)
eval (Inv x) = inv (eval x)
eval (Embed x) = x


-- How to promote this to equations with unknowns, at the type level?
