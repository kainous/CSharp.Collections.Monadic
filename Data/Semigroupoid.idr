import Builtins
--import Data.HomSet

%access public export
%default total

infixl 2 <>

infixl 4 <*, *>

--postulate
--funext : {f, g : a -> b} -> ((x: a) -> f x = g x) -> f = g

data MagmaDuality : ty -> Type where
  M : (ty -> ty -> ty) -> MagmaDuality ty
  D : (ty -> ty -> ty) -> MagmaDuality ty

dual : MagmaDuality ty -> MagmaDuality ty
dual (M f) = D (\a, b => f b a)
dual (D f) = M (\a, b => f b a)

data B = T | F

--and : B -> B -> B
--and T _ = T
--and F x = x

--andDual : B -> B -> B
--andDual _ T = T
--andDual x F = x

not : B -> B
not T = F
not F = T

notD : B -> B
notD T = F
notD F = T


interface Magma ty where
  constructor MkMagma
  (*>) : ty -> ty -> ty

interface DualMagma ty where
  (<*) : ty -> ty -> ty

--data DualMagma : ty -> Type where
--  GetDualMagma : Magma m -> DualMagma m

--Magma ty => DualMagma ty where
--  a <* b = b *> a

--DualMagma ty => Magma ty where
--  a *> b = b <* a

Dual : {ty : Type} -> Type -> Type
Dual Magma {ty} = DualMagma ty
--Dual DualMagma ty = Magma ty


And : Magma B
And = MkMagma $ \x, y => case x of
                          T => T
                          F => y

--Conv : DualMagma B
--Conv = Dual And

--Magma B where
--  a *> b = ?rhs

--data MagmaDuality : (Magma a ** Magma a)

--data Arr : obj -> obj ->
--data Arr obj = obj -> obj -> Type

interface Magmoid (arr : obj -> obj -> Type) where
  (>>) : arr a b -> arr b c -> arr a c

interface DualMagmoid (arr : obj -> obj -> Type) where
  (<<) : arr b c -> arr a b -> arr a c

--test56 : x => (Magmoid x ** DualMagmoid x)

--data MagmoidDuality : (Magmoid arr ** DualMagmoid arr) -> Type where
--  GetDuality : x -> MagmoidDuality x

data BoolArrow : () -> () -> Type where
  GetBool : B -> BoolArrow () ()

--Magmoid BoolArrow where
--  (GetBool T) >> (GetBool T) = GetBool T
--  (GetBool F) >> (GetBool x) = GetBool x

--DualMagmoid BoolArrow where
--  (GetBool T) << (GetBool T) = GetBool T
--  (GetBool F) << (GetBool x) = GetBool x

--test4 : (m : Magmoid a ** DualMagmoid a)
--test4 = (BoolArrow ** BoolArrow)

--Dual : (arr : obj -> obj -> Type) => (m : Magmoid arr ** DualMagmoid arr) => Type -> y -> Type
--Dual Magmoid a = DualMagmoid ?rhs7 -- {obj} ?rhs5
--Dual DualMagmoid k a b = Magmoid {obj} ?rhs6
--Dual (DualMagmoid) = Magmoid
--Dual Magmoid y = z where
--Dual (_ ** _) DualMagmoid = Magmoid a

{-
Magmoid arr => DualMagmoid arr where
  g << f = f >> g

DualMagmoid arr => Magmoid arr where
  f >> g = g << f

interface Magmoid arr => Semigroupoid (arr : obj -> obj -> Type) where
  associativeComposition : (f : arr a b) -> (g : arr b c) -> (h : arr c d) -> f >> (g >> h) = (f >> g) >> h

interface Semigroupoid arr => Category (arr : obj -> obj -> Type) where
  id : arr a a
  leftIdentity  : {f : arr a b} -> id >> f = f
  rightIdentity : {f : arr a b} -> f >> id = f

interface Magma ty where
  (<>) : ty -> ty -> ty

data MagmaArrow : ty -> () -> () -> Type where
  AsMagmoid : Magma ty => ty -> MagmaArrow ty () () -}

---Magmoid (MagmaArrow ty) where
--  (AsMagmoid a) >> (AsMagmoid b) = AsMagmoid (a <> b)

--interface Magma ty => Semigroup ty where
--  associative : {a, b, c : ty} -> a <> (b <> c) = (a <> b) <> c

--data SemigroupArrow : ty -> () -> () -> Type where
--  AsSemigroupoid : Semigroup ty => ty -> SemigroupArrow ty () ()

--Semigroupoid (Semigroup ty) where
  --associativeComposition _ = ?rhs6

--interface Semigroup ty => Monoid ty where


infixl 1 +
data Nat = Z | S Nat

(+) : Nat -> Nat -> Nat
a + Z = a
a + (S b) = S (a + b)


--data NatArrow : () -> () -> Type where
--  GetNat : Nat -> NatArrow () ()

--Semigroupoid' NatArrow where
--  (GetNat a) >> (GetNat b) = GetNat (a + b)

--data SemigroupArrow : ty -> () -> () -> Type where
--  AsSemigroupoid : Semigroup ty => ty -> SemigroupArrow ty () ()

--Magmoid (SemigroupArrow ty) where
--  (AsSemigroupoid a) >> (AsSemigroupoid b) = AsSemigroupoid (a <> b)

{-
interface Magmoid (arr : obj ~> obj ~> Type) where
  (>>) : arr a b -> arr b c -> arr a c

interface Magmoid arr => LeftSemigroupoid (arr : obj ~> obj ~> Type) where
  leftAssociativity : {f : arr a b} -> {g : arr b c} -> {h : arr c d} -> f >> g -> arr b d -> (f >> (g >> h)) = ((f >> g) >> h)

  la : {a : obj} -> (f : arr a b) -> (g : arr b c) -> (h : arr c d) -> f >> (g >> h) = (f >> g) >> h
--  leftAssociativity : () -- {a, b, c, d : obj} -> (f : arr a b) -> (g : arr b c) -> (h : arr c d) -> ((f >> g), (g >> h)) -> (f >> (g >> h)) = ((f >> g) >> h)

--interface DualMagmoid (arr : obj -> obj -> Type) where



interface PartialOrder (ord : ty -> ty -> Type) where
  --reflexive     : ord a a
  --antisymmetric : ord a b -> ord b a -> a = b
  transitive    : ord a b -> ord b c -> ord a c

interface DirectedConnection (arr : obj -> obj -> Type) where
  to : {a, b, c : obj} -> arr a b -> arr b c -> arr a c
-}
-- Here's the rub, not all connections are evaluative (like partial orders), and composition still doesn't make it evaluative

--interface Magmoid (arr : obj -> obj -> Type) where
--  (>>) : arr a b ->

--interface Semigroupoid (arr : obj -> obj -> Type) where
--  (>>) : arr a b -> arr b c -> arr a c

--Semigroupoid (PartialOrder ord) where
--  transitive f g = f >> g



{-
interface DirectedConnection arr => Semigroupoid' (arr : obj -> obj -> Type)

interface DirectedConnection arr => Semigroupoid (arr : obj -> obj -> Type) where
  associative : (f : arr a b) -> (g : arr b c) -> (h : arr c d) -> f `to` (g `to` h) = (f `to` g) `to` h

(>>) : Semigroupoid' arr => arr a b -> arr b c -> arr a c

interface Semigroupoid' arr => Category' (arr : obj -> obj -> Type) where
  unit : (a : obj) -> arr a a

interface (Semigroupoid arr, Category' arr) => Category (arr : obj -> obj -> Type) where
  leftUnitary  : {a, b : obj} -> (f : arr a b) -> unit a >> f         = f
  rightUnitary : {a, b : obj} -> (f : arr a b) ->      f >> unit b = f
-}
