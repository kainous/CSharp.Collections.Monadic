--interface Bifunctor (p : obj -> obj -> Type) where
--  bimap : {a, a', b, b' : obj} -> (a -> a') -> (b -> b') -> (p a b -> p a' b')

--interface Profunctor (p : obj -> obj -> Type) where
--  dimap : {a, a', b, b' : obj} -> (a' -> a) -> (b -> b') -> (p a b -> p a' b')

interface Bifunctor (p : Type -> Type -> Type) where
  bimap : (a -> a') -> (b -> b') -> (p a b -> p a' b')

interface Profunctor (p : Type -> Type -> Type) where
  dimap : (a' -> a) -> (b -> b') -> (p a b -> p a' b')

infixr 4 ~>

data Morphism a b = Mor (a -> b)
(~>) : Type -> Type -> Type
(~>) = Morphism

Bifunctor (~>) where
  bimap f g (Mor h) = Mor (\x => ?rhs)

Profunctor (~>) where
  dimap f g (Mor h) = Mor (\x => g (h (f x)))

interface (Category p, Profunctor p) => Arrow p where

interface Category p => Prearrow p where
  arr : (a -> b) -> p a b

dimap' : Prearrow p => (i' -> i) -> (o -> o') -> p i o -> p i' o'
dimap' l r f = arr r << f << arr l
