infixl 4 :<-, <<

data (:<-) = W (b -> a)
data Morphism = Mor (a -> b)

(<<) : (b -> c) -> (a -> b) -> a -> c
g << f = \x => g (f x)

--data Procompose p q d c where
--  Procomp : p x c -> q d x -> Procompose p q d c

interface Profunctor (h : obj -> obj -> Type) where
  dimap : {a, b, c, d : obj} -> (a -> b) -> (c -> d) -> h b c -> h a d
  --lmap : {d', d, c, c': obj} -> (d' -> d) -> h d c -> h d' c
  --rmap : (c  -> c') -> h d c -> h d c'

--  lmapUnit : lmap id = id
--  rmapUnit : rmap id = id

  --dimap f g = lmap f << rmap g

--interface PFunctor (r : obj -> obj -> Type) (t : obj -> obj -> Type) where
---  first : (r a b) -> t (p a c) (p b c)

--instance Profunctor h => PFunctor h (:<-) (Morphism) where first = lmap >> W

--instance Profunctor h => QFunctor h (:<-) (Morphism) where second = rmap
