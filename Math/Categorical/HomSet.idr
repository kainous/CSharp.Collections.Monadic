import Builtins

infixr 4 ~>

data (~>) a b = Mor (a -> b)

implicit
toMorphism : (a -> b) -> (a ~> b)
toMorphism f = Mor f

data Unit = MkUnit

data B = T | F

not : B -> B
not T = F
not F = T

--const : a -> (b -> a)
--const x _ = x

--infixl 4 |>
(|>) : a -> (a ~> b) -> b
x |> (Mor f) = f x

notM : B ~> B
notM = Mor not

test0 : B
test0 = T |> notM
