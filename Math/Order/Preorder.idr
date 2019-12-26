%default total

infixl 4 ==

interface PreorderedSet (rel : obj -> obj -> Type) where
  total transitivity : rel a b -> rel b c -> rel a c
  total reflexivity  : (a : obj) -> rel a a

PreorderedSet (=) where
  reflexivity _ = Refl
  transitivity Refl Refl = Refl

interface PreorderedSet rel => Poset (rel : obj -> obj -> Type) where
  total antisymmetry : rel a b -> rel b a -> a = b

interface PreorderedSet rel => Equivalence (rel : obj -> obj -> Type) where
  total symmetry : rel a b -> rel b a

--Equivalence (=) where
--  symmetry Refl = Refl

--(==) : Type
--(==) = Equivalence

data (==) : obj -> obj -> Type where
  Refl : (a : obj) -> (b : obj) -> a == b

PreorderedSet (==) where
  reflexivity a = Refl a a
  transitivity (Refl a b) (Refl b c) = Refl a c

Equivalence (==) where
  symmetry (Refl a b) = Refl b a

data B = T | F

data LTE : (p, q : B) -> Type where
  No  : LTE T F
  Yes1 : LTE T T -> LTE T T
  Yes2 : LTE F x -> LTE F x

imp : B -> B -> B
imp T F = F
imp _ _ = T

mytran : (p : B) -> (q : B) -> (r : B) -> LTE p q -> LTE q r -> LTE p r
mytran T T r x y = ?mytran_rhs_3
mytran T F r x y = ?mytran_rhs_4
mytran F q r x y = ?mytran_rhs_2



--PreorderedSet LTE where
--  reflexivity a = Yes
--  transitivity = ?rhs1234-- mytran
