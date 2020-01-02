module Data.HomSet

import Builtins

%access public export
%default total

-- In the category of objects, a morphism, containing a domain and a codomain, as objects, is isomorphic to Pair
-- and as such, doesn't have to be defined on its own. Instead, a more general notion of category is required, and is
-- given here. This is more restrictive than Pair, requiring that both items be of the same object type. It is exactly
-- as restrictive if
--data Morphism : obj -> obj -> Type

-- General morphisms are isomorphic to Pair, and as such, we do not need to name dom and cod for Morphisms.



--data MyMorphism : obj -> obj -> Type where
--  MyMor : a -> b -> MyMorphism a b

--fiber : {x : a} -> (a -> b) -> MyMorphism a b
--fiber {x} f b = MyMor x (f x)


-- note that since function arrows are left right associative, this is not the same as (a -> b) -> ... any function from a to b
-- In other words, Morphism, as defined above, is more like a dictionary of dictionaries

--dom : MyMorphism a b -> a
--dom (MyMor x _) = x

--cod : MyMorphism a b -> b
--cod (MyMor _ y) = y

--test0 : MyMorphism Unit String
--test0 = MyMor () "Hello"

-- This is no different than Pair where fst and snd


infixr 4 ~>
||| HomSet
data Morphism : Type -> Type -> Type where
  Mor : (a -> b) -> Morphism a b

--data Endomorphism : Type where
--  Endo : (a -> a) -> Endomorphism a

(~>) : Type -> Type -> Type
(~>) = Morphism

--(>>) : Type -> Type -> Type
--f >> g = ?rhsmor --a ~> c


(<|) : (a ~> b) -> a -> b
(Mor f) <| x = f x

(|>) : a -> (a ~> b) -> b
x |> (Mor f) = f x

id : (a:Type) -> (a ~> a)
id a = Mor id

--interface Involutive a where
--  morphism   : a ~> a
--  involution : x = x |> morphism |> morphism

--interface StarSemigroup ty where
--  star : ty -> ty
--  op   : ty -> ty -> ty
--  antihomomorphism : star (a `op` b) = (star b) `op` (star a)

--conjugate : StarGroup ty => (a : ty) -> (b : ty) -> ty
--conjugateBy a b = a * b * (inv a)


--flip : (a ~> b ~> c) ~> (b ~> a ~> c)
--flip = Mor (\(Mor g) => z)
--  where
    --g (\x => ?rhs)
    --?rhs2

    --theorem : {f : (a -> b) -> c} -> f = (\g => f (\x => g x))
    --theorem = funext $ \g => Refl

pointfulComposition : (f : a -> b) -> (g : b -> c) -> (x : a) -> g (f x) = (f >> g) x
pointfulComposition f g x = Refl

--step_1 : (f : a -> b) -> (prf : g = h) -> (x : a) -> (\x1 => g (f x1)) x = (\x1 => h (f x1)) x
--step_1 f prf x = cong funext (?rhs)

--leftExtensionality : {g : b -> c} -> {h : b -> c} -> (f : a -> b) -> g = h -> f >> g = f >> h
--leftExtensionality f prf = qed where
  --step_1 : (x : _) ->
--  qed = funext (\x => step_1 f prf x)

eqConst : (a = b) -> c -> (a = b)
eqConst prf = \_ => prf

rightComposition : {f, g : a -> b} -> {h : b -> c} -> f = g -> f >> h = g >> h
rightComposition Refl = Refl

leftComposition : {f, g : b -> c} -> {h : a -> b} -> f = g -> h >> f = h >> g
leftComposition Refl = Refl

associativityOfFunctions : (f : a -> b) -> (g : b -> c) -> (h : c -> d) -> f >> (g >> h) = (f >> g) >> h
associativityOfFunctions f g h = Refl

flip : (a -> b -> c) -> (b -> a -> c)
flip f x y = f y x

--flipFlip : {f : a -> b -> c} -> f = flip (flip f)
--flipFlip = funext <| \_ => (funext <| \_ => Refl)



--const : a -> (b ~> a)
--const = Mor (\x, y => x)


interface Functor (f : Type -> Type) where
  map : (func : a -> b) -> f a -> f b

Functor (Morphism r) where
  map f (Mor g) = Mor (\x => f (g x))

--Functor (id t) where
--  map = id

-- first obj can be implicit here.
interface Category obj (arr : obj -> obj -> Type) where
  cId : (a : obj) -> arr a a
  cComp : {a, b, c : obj} -> arr b c -> arr a b -> arr a c
  cCompAssociative : (f : arr a b) -> (g : arr b c) -> (h : arr c d) -> h `cComp` (g `cComp` f) = (h `cComp` g) `cComp` f

  cIdRight : {a, b : obj} -> (f : arr a b) -> f = f `cComp` (cId a)
  cIdLeft  : {a, b : obj} -> (f : arr a b) -> f = cId b `cComp` f

infixl 6 .
(.) : (b -> c) -> (a -> b) -> a -> c
f . g = \x => f (g x)


--Category Type Morphism where
--  cComp = \x => g (f x)
--  cId = Mor ?id2 -- id
--  cCompAssociative (Mor f) (Mor g) (Mor h) = ?rhsass
--  cIdRight = ?rhsright
--  cIdLeft = ?rhsLeft
