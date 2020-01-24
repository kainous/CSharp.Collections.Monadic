module Math.Functorial.Functor

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid
import Math.Categorical.Category

%default total
%access public export

infixr 4 ~>

data (~>) a b = Mor (a -> b)

interface (RawCategory cat1, RawCategory cat2) =>
  RawGenFunctor
    (f : obj1 -> obj2)
    (cat1 : obj1 -> obj1 -> Type)
    (cat2 : obj2 -> obj2 -> Type) where
  genMap : cat1 a b -> cat2 (f a) (f b)

interface (RawCategory cat1, RawCategory cat2) =>
  RawGenCofunctor
    (f : obj1 -> obj2)
    (cat1 : obj1 -> obj1 -> Type)
    (cat2 : obj2 -> obj2 -> Type) where
  genComap : cat1 b a -> cat2 (f a) (f b)

--interface RawThinFunctor (f : Type -> Type) where
--  map : (a -> b) -> (f a -> f b)

interface RawGenFunctor f source target => GenFunctor (f : obj -> obj') (source : obj -> obj -> Type) (target : obj' -> obj' -> Type) where
  -- does this property not inherit from Category???
  idPreservation1 : {x : obj} -> {y : obj'} -> f x = y -> f (id x) = id y
  idPreservation2 : {x : obj} -> {y : obj'} -> f (id x) = id y -> f x = y
  composePreservation : {g : t -> u} -> {h : u -> obj} -> f ((g >> h) x) = ((\y => f (g y)) >> (\z => f (h z))) -- (compose (\u => f (g u)) (\v => f (h v))) y

interface RawGenFunctor f cat cat => Endofunctor (f : obj -> obj) (cat : obj -> obj -> Type)

interface (RawCategory cat1, RawCategory cat2, RawCategory cat3) => RawGenBifunctor (f : obj1 -> obj2 -> obj3) (cat1 : obj1 -> obj1 -> Type) (cat2 : obj2 -> obj2 -> Type) (cat3 : obj3 -> obj3 -> Type) where
  bimap : cat1 a1 b1 -> cat2 a2 b2 -> cat3 (f a1 a2) (f b1 b2)

-- There is a lattice on this
data Variance
  = Phantom
  | Invariant
  | Covariant
  | Contravariant

---data List a = Nil | Cons a (List a)

data List : (elem : Type) -> Type where
  Nil : List elem
  Cons : (x : elem) -> (xs : List elem) -> List elem

interface (RawCategory cat1, RawCategory cat2, RawCategory cat3) => Bifunct (f : obj1 -> obj2 -> obj3) (cat1 : obj1 -> obj1 -> Type) (cat2 : obj2 -> obj2 -> Type) (cat3 : obj3 -> obj3 -> Type) where
  bimap : cat1 a1 b1 -> cat2 a2 b2 -> cat3 (f a1 a2) (f b1 b2)
data Manifest : Type where
  NilM  : Manifest
  ConsM : Variance -> (cat : obj -> obj -> Type) -> Manifest -> Manifest

--[Variance, RawCategory cat]

data LiftedFunctor : Type -> Type where
  Lift : (f : Type -> Type) -> (a : Type) -> LiftedFunctor (f a)

interface (RawCategory cat1, RawCategory cat2, RawCategory cat3) => RawGenProfunctor (f : obj1 -> obj2 -> obj3) (cat1 : obj1 -> obj1 -> Type) (cat2 : obj2 -> obj2 -> Type) (cat3 : obj3 -> obj3 -> Type) where
  dimap : cat1 b1 a1 -> cat2 a2 b2 -> cat3 (f a1 a2) (f b1 b2)

infixr 4 ~>
data (~>) a b = Mor (a -> b)

Magmoid (~>) where
  compose (Mor f) (Mor g) = Mor (f >> g)

RawSemigroupoid (~>) where
--  compositionIsAssociative = ?rhs

RawCategory (~>) where
  id = Mor id


test0 : Manifest
test0 = ConsM Phantom (~>) (ConsM Invariant (~>) NilM)

partial
headM : Manifest -> Variance
headM (ConsM x cat y) = x

data Either a b = Left a | Right b

RawGenBifunctor Pair (~>) (~>) (~>) where
  bimap (Mor f) (Mor g) = Mor (\(x, y) => (f x, g y))


--interface RawGenFunctor f (~>) (~>) => BaseFunc (f : Type -> Type) where

interface BaseFunctor (f : Type -> Type) where
  mmap : (a -> b) -> f a -> f b

BaseFunctor f => RawGenFunctor f (~>) (~>) where
  map (Mor g) = Mor (\x => mmap g x)
RawGenBifunctor Either (~>) (~>) (~>) where
  bimap (Mor f) (Mor g) = Mor (\x => case x of
                                     Left a => Left (f a)
                                     Right b => Right (g b))

ToFunctor : Manifest -> Type -> Type
ToFunctor NilM y = y
--ToFunctor (ConsM x cat z) y = cat -> (ToFunctor z y)

test2 : Type
test2 = ToFunctor NilM (Either () ())


namespace Functor
  interface RawFunctor (w : Type -> Type) where
    map : (a -> b) -> w a -> w b

infixr 4 !>, <!, $>, <$

-- We use the notation !> to mean "unwrap, then apply, then wrap"

(<!) : RawFunctor w => (a -> b) -> w a -> w b
(<!) = map

(!>) : RawFunctor w => w a -> (a -> b) -> w b
(!>) = flip map

(<$) : RawFunctor w => a -> w b -> w a
(<$) = map << const

($>) : RawFunctor w => w a -> b -> w b
($>) = flip (<$)

mapid : RawFunctor w => (x : w a) -> w a
mapid = map id

interface RawFunctor w => Functor (w : Type -> Type) where
  preservesIdentity    : (x : w a) -> mapid x = x
  preservesComposition :
    .{f : a -> b} ->
    .{g : b -> c} ->
    -- We use the x to specify which (functor) map we want to use, and to make
    --  proofs easier by forcing you to pattern match on it
    (x : w a) ->
    (map (f >> g)) x = (map f >> map g) x

-- Why does this only apply to the second argument?
RawFunctor (Pair a) where
  map f (x, y) = (x, f y)

--test0 : Morf B B
--test0 = map negate negate


data NaturalTransformation : (obj -> Type) -> (obj -> Type) -> Type where
  MkNaturalTransformation : (f : obj -> Type) -> (g : obj -> Type) -> NaturalTransformation f g


data NaturalComposition : Type -> Type -> Type where
  MkNaturalComposition : (f, f', g, g' : Type -> Type) -> (a:Type) -> NaturalComposition (f' (f a)) (g' (g a))

-- Bring forward adjunctions
-- http://www.stephendiehl.com/posts/adjunctions.html
--vert :
  --(Functor f, Functor f', Functor g, Functor g') =>
  --NaturalTransformation f' g' ->
  --NaturalTransformation f  g  ->
  --NaturalComposition f f' g g'



data ListF a x = NilF | ConsF a x

--data Fix f = f (Fix f)
--data Lis a = Fix (ListF a)
--Monoid a => Monad (Pair a) where
--  join (x, (y, z)) = (x <> y, z)
--  wrap x = (neutral, x)
