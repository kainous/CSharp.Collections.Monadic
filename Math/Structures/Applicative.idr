infixl 4 <|, |>
infixl 3 <<, >>

flip : (a -> b -> c) -> (b -> a -> c)
flip f x y = f y x

interface Apply (f : Type -> Type) where
  apply : f (a -> b) -> f a -> f b

(<|) : Apply f => f (a -> b) -> f a -> f b
(<|) = apply

(|>) : Apply f => f a -> f (a -> b) -> f b
(|>) = flip apply

--interface Applicative

--(>>) : Apply m => m (a -> b) -> m (b -> c) -> m (a -> c)
--f >> g = \x => ?rhs-- x |> f |> g)
