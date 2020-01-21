
data Nat = Z | S Nat
data Pair a b = MkPair a b

data Unit = MkUnit

data Morphism a b = Mor (a -> b)

infixr 4 ::

data Vect : (len : Nat) -> (elem : Type) -> Type where
  Nil : Vect Z elem
  Cons : (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem

data HVect : Vect k Type -> Type where
  HNil : HVect []
  (::) : t -> HVect ts -> HVect (Cons t ts)

data Variance
  = Covariant
  | Contravariant
  | Phantom
-- This is similar to Pos | Neg | Zero

Mapping : Variance -> Type -> Type -> Type
Mapping Phantom       a b = Unit
Mapping Covariant     a b = a -> b
Mapping Contravariant a b = b -> a

infixl 4 :^:

--data Mappings : Vect n Variance -> Type -> Type -> Type where
--  M0    : Mappings [] x y
--  (:^:) : Mapping v a b -> Mappings vs as bs -> Mappings (Cons v vs) (Cons a as) (Cons b bs)

--data Tst : (Type -> Type) -> Variance -> Type where
--  TCons : (f : a -> b) -> Variance -> Tst (f )

Test : Variance -> (Type -> Type) -> Continuation


-- Covariant
interface EFunctor (f : Type -> Type) where
  map : (a -> a') -> (f a -> f a')

-- Covariant, Covariant
interface EBifunctor (f : Type -> Type -> Type) where
  bimap : (a -> a') -> (b -> b') -> (f a b -> f a' b')

-- Contravariant, Covariant
interface EProfunctor (f : Type -> Type -> Type) where
  dimap : (a -> a') -> (b -> b') -> (f a' b -> f a b')

interface ETrifunctor (f : Type -> Type -> Type -> Type) where
  trimap : (a -> a') -> (b -> b') -> (c -> c') -> (f a b c -> f a' b' c')

interface KEndoFunctor (f : Type -> Type) (v : Vect n Variance) where
  kmap : Mapping v as bs -> f as -> f bs





  --interface (RawCategory xcat, RawCategory ycat) => RawGenFunctor (f : xobj -> yobj) (xcat : xobj -> xobj -> Type) (ycat : yobj -> yobj -> Type) | f where
  --  map : xcat a b -> ycat (f a) (f b)
