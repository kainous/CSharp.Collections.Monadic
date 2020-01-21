module Math.Order.Preorder

import Builtins
import Prelude.Either

%default total
%access public export

infixl 4 ==

--data B = T | F
--compose : {rel : a -> b -> B} ->

-- This requires Categories to implement
--tran : {rel : Type -> Type -> Type} -> (f : rel a b) -> (g : rel b c) -> rel a (rel b c)
--tran f g = \x => rel x ?tranrhs

data Reverse rel a b = MkReverse rel b a

-- Currying specifically tells us that order relations may be endo, but relations in general are not
-- Currying is a kind of transitivity on the composition between relations
-- However, a relation, that is not endo, is basically equivalent to Pair a b
--curry : {rel : Type -> Type -> Type} -> rel a (rel b c) -> rel (a, b) c
--curry x = ?curry_rhs_1

--uncurry : {rel : obj -> obj -> Type} -> rel a (rel b c) ->

-- If you are curious how relations word, defined this way, remember that a relation is often
-- defined as a subset of the cartesian product of sets (i.e. R ⊆ U × V), and that a subset
-- can be defined according to a indicator function (U × V → Bool). However, since
-- we are working in the "Proposition as Types" domain, and our propositions aren't Bool,
-- but are instead "Type", then we have (U × V → Type). Last tweak we use is to curry
-- this into a curried function.

Asymm : (rel : obj -> obj -> Type) -> obj -> obj -> Type
Asymm rel a b = (rel a b, Not (rel b a))

interface Quasitransitive (rel : obj -> obj -> Type) where
  quasitran : Asymm rel a b -> Asymm rel b c -> Asymm rel a c

interface Symmetric (rel : obj -> obj -> Type) where
  sym : rel a b -> rel b a

interface Asymmetric (rel : obj -> obj -> Type) where
  asym : Asymm rel a b

interface Reflexive (rel : obj -> obj -> Type) where
  refl : rel a a

interface Irreflexive (rel : obj -> obj -> Type) where
  irrefl : (a : obj) -> Not (rel a a)



interface Transitive (rel : obj -> obj -> Type) where
  trans : rel a b -> rel b c -> rel a c

interface Cotransitive (rel : obj -> obj -> Type) where
  cotrans : rel a b -> Either (rel a c) (rel b c)

--interface => Semiorder (rel : obj -> obj -> obj) where
interface (Irreflexive rel, Symmetric rel, Cotransitive rel) => AppartnessRelation (rel : obj -> obj -> Type) where
interface (Transitive rel, Reflexive rel) => PreorderedSet (rel : obj -> obj -> Type) where
interface (Symmetric rel, Transitive rel) => PartialEquivalenceClass (rel : obj -> obj -> Type) where
interface (Irreflexive rel, Transitive rel) => StrictOrder (rel : obj -> obj -> Type) where
interface (PreorderedSet rel, PartialEquivalenceClass rel) => EquivalenceClass (rel : obj -> obj -> Type) where

interface EquivalenceClass rel => Congruence (rel : obj -> obj -> Type) where
  cong : .{a, b : obj} -> (f : obj -> obj) -> rel a b -> rel (f a) (f b)

  --interface Antisymmetric (rel : obj -> obj -> Type) where
  --  antisym : rel a b -> rel b a -> a = b


--StrictOrder rel => Asymmetric rel where
--  asym x = ?rths

Reflexive (=) where
  refl = Refl

Symmetric (=) where
  sym Refl = Refl

Transitive (=) where
  trans Refl Refl = Refl

PartialEquivalenceClass (=) where
PreorderedSet (=) where
EquivalenceClass (=) where
Congruence (=) where
  cong _ Refl = Refl

-- Antisymmetry wrt a equivalance class
interface EquivalenceClass eq => Antisymmetric (eq : obj -> obj -> Type) (rel : obj -> obj -> Type) where
  antisym : {x, y : obj} -> rel x y -> rel y x -> eq x y

Asymmetric rel => Antisymmetric eq rel where


data Dec : Type -> Type where
  Yes : (prf : prop)        -> Dec prop
  No  : (contra : Not prop) -> Dec prop

interface DecEq t where
  decEq : (a, b : t) -> Dec (a = b)

--interface Poset
{-
PreorderedSet (=) where
  reflexivity _ = Refl
  transitivity Refl Refl = Refl

interface (PreorderedSet rel, Antisymmetric rel) => Poset (rel : obj -> obj -> Type) where
interface (PreorderedSet rel, Symmetric rel) => Equivalence (rel : obj -> obj -> Type) where

Equivalence (=) where
  symmetry Refl = Refl

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
-}
{-
data Implication : (p, q : B) -> Type where



  No  : LTE T F
  Yes1 : LTE T T -> LTE T T
  Yes2 : LTE F x -> LTE F x

imp : B -> B -> B
imp T F = F
imp _ _ = T

mytran : (p : B) -> (q : B) -> (r : B) -> LTE p q -> LTE q r -> LTE p r
mytran T T r No y = ?mytran_rhs_3
mytran T T r (Yes1 x) y = ?mytran_rhs_4
mytran T F r x y = ?mytran_rhs_4
mytran F q r x y = ?mytran_rhs_2
-}


--PreorderedSet LTE where
--  reflexivity a = Yes
--  transitivity = ?rhs1234-- mytran
