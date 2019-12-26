infixl 4 <|, |>
infixl 3 <<, >>

flip : (a -> b -> c) -> (b -> a -> c)
flip f x y = f y x

interface Pointed (p : Type -> Type) where
  wrap : a -> p a

interface Apply (f : Type -> Type) where
  apply : f (a -> b) -> f a -> f b

(<|) : Apply f => f (a -> b) -> f a -> f b
(<|) = apply

(|>) : Apply f => f a -> f (a -> b) -> f b
(|>) = flip apply

interface Category (arr : obj -> obj -> Type) where
  id : arr a a
  compose : arr b c -> arr a b -> arr a c

(>>) : Category arr => arr a b -> arr b c -> arr a c
(>>) = flip compose

(<<) : Category arr => arr b c -> arr a b -> arr a c
(<<) = compose

record KleisiMorphism (f : Type -> Type) a b where
  constructor Kleisi
  apply : a -> f b

interface Pointed m => Monad (m : Type -> Type) where
  bind : (a -> m b) -> m a -> m b

Monad m => Category (KleisiMorphism m) where
  id = Kleisi (wrap ?rhs2) --(wrap << id)
  compose (Kleisi f) (Kleisi g) = Kleisi ?rhs -- <| \a => (bind f (g a))



--Apply m  => Category where


--interface Applicative

--(>>) : Apply m => m (a -> b) -> m (b -> c) -> m (a -> c)
--f >> g = \x => ?rhs-- x |> f |> g)

--(>>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)

interface Transform a ty where
  transform : a -> ty -> ty

--interface Magma ty -> Transform ty ty where
