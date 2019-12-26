import Builtins


--funext : (f, g : a -> b) -> ((x:a) -> f x = g x) -> f = g
--funext f g = believe_me

postulate
funext2 : (f, g : a -> b -> c) -> ((x : a) -> (y : b) -> f x y = g x y) -> f = g

flip : (a -> b -> c) -> b -> a -> c
flip f a b = f b a

--using (arr : obj -> obj -> Type)
--  data Yoneda : arr a b -> arr a b -> Type where
    --GetYoneda : arr a b -> Yoneda (arr a b)

data Yoneda : (f : Type -> Type) -> (a : Type) -> Type where
  Yon : ({b : Type} -> (a -> b) -> f b) -> Yoneda f b

Op : (Type -> Type) -> Type -> Type
Op (Yon s) = ?Op_rhs_2

--Op p = Yoneda p

--interface Category' (arr : obj -> obj -> Type) where
--  id : arr a a
