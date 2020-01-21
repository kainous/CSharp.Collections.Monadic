
infixr 4 ===>

data (===>) a b = Mor (a -> b)

data Expr : Type -> Type where
  K : a -> b -> Expr (a ===> b ===> a)
  S : a -> b -> c -> Expr ((a ===> b ===> c) ===> (a ===> b) ===> (a ===> c))
  App : a -> b -> Expr (a ===> b) -> Expr a -> Expr b
