module Data.HomSet

import Builtins

%access public export
%default total


infix 4 ~>
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


Category Type Morphism where
  cComp = \x => g (f x)
  cId = Mor ?id2 -- id
  cCompAssociative (Mor f) (Mor g) (Mor h) = ?rhsass
  cIdRight = ?rhsright
  cIdLeft = ?rhsLeft
