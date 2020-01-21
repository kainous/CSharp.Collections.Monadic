data Expr a
  = Sum (Expr a) (Expr a)
  | Pair (Expr a) (Expr a)
  | Void
  | Unit

data Bool = True | False

and : Bool -> Bool -> Bool
and True  x = x
and False _ = False

isEq : Expr a -> Expr a -> Bool
isEq Void Void = True
isEq Unit Unit = True
isEq (Sum x y) (Sum x' y') = isEq x x' `and` isEq y y'
isEq _ _ = False

derivative : Expr a -> Expr a -> Expr a
derivative Void _ = Void
derivative Unit _ = Void
derivative x dx with (isEq x dx)
  | True = Unit
derivative (Sum x y) dt = Sum (derivative x dt) (derivative y dt)
derivative (Pair x y) dt = Sum (Pair (derivative x dt) y) (Pair x (derivative y dt))
