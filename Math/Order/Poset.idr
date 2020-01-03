import Builtins
import Math.Categorical.Category

infixl 4 <>
infixl 13 <=, >=, >, <
infixl 14 ==, /=
interface Monoid ty where
  (<>) : ty -> ty -> ty
  neutral : ty

data Ordering = LT | GT | EQ

data Bool = True | False

--defined to make pairing work
Monoid Ordering where
  LT <> _ = LT
  GT <> _ = GT
  EQ <> b = b

  neutral = EQ

interface Ord ty where
  (<=)    : ty -> ty -> Bool
  compare : ty -> ty -> Ordering

  compare x y =
    case (x <= y, y <= x) of
    (True, True)  => EQ
    (True, False) => LT
    (False, _)    => GT

  a <= b =
    case compare a b of
    LT => True
    EQ => True
    GT => False


(>=) : Ord ty => ty -> ty -> Bool
(>=) = flip (<=)

(<) : Ord ty => ty -> ty -> Bool
a < b =
  case compare a b of
  GT => True
  LT => False
  EQ => False

(>) : Ord ty => ty -> ty -> Bool
(>) = flip (<)

{- (Ord a, Ord b) => Ord (a, b) where
  compare (x, y) (x', y') =
    case compare x x' of
    LT => LT
    GT => GT
    EQ => compare y y' -}

data Either a b
  = Left a
  | Right b

-- These are the same axioms for a category
-- preorders don't have an algebraic proof of the neutrality of id
-- Is it better to make preorder inherit from Category or to make it implement category?
interface Preorder obj (ord : obj -> obj -> Type) where
  total reflexivity  : {a : obj} -> ord a a
  total transitivity : {a, b, c : obj} -> ord a b -> ord b c -> ord a c

--Category {obj} mor => Preorder obj mor where
--  reflexivity  = id {obj}
--  transitivity = compose

interface Preorder obj ord => Poset obj (ord : obj -> obj -> Type) where
  total antisymmetry : {a, b : obj} -> ord a b = ord b a

interface (Poset obj ord) => Ordered obj (ord : obj -> obj -> Type) where
  total order : (a, b : obj) -> Either (ord a b) (ord b a)

interface (Preorder obj eq) => Equivalence obj (eq : obj -> obj -> Type) where
  total symmetry : {a, b : obj} -> eq a b -> eq b a

interface (Equivalence obj eq) => Congruence obj (f : obj -> obj) (eq : obj -> obj -> Type) where
  total congruent : {a, b : obj} -> eq a b -> eq (f a) (f b)

min : (Ordered ty ord) => ty -> ty -> ty
min {ord} x y with (order {ord} x y)
  | Left  _ = x
  | Right _ = y

max : (Ordered ty ord) => ty -> ty -> ty
max {ord} x y with (order {ord} x y)
  | Left  _ = y
  | Right _ = x

Preorder ty ((=) {A=ty} {B=ty}) where
  reflexivity = Refl
  transitivity {a} {b} {c} = trans {a = a} {b = b} {c = c}

Equivalence ty ((=) {A=ty} {B=ty}) where
  symmetry prf = sym prf

Congruence ty f ((=) {A=ty} {B=ty}) where
  congruent {a} {b} = cong {a = a} {b = b} {f = f}

--Ordered ty ord => Ord ty where
--  a <= b = ?rhs
    --case order {ord} a b of
    --| Left  _ = True
    --| Right _ = False
