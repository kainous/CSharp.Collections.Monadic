module Math.Functorial.Functor

import Builtins
import Math.Categorical.Category

%default total
%access public export

interface RawGenFunctor (f : obj -> obj') (source : obj -> obj -> Type) (target : obj' -> obj' -> Type) where
  map : source a a' -> target (f a) (f a')

interface RawGenFunctor f cat cat => Endofunctor (f : obj -> obj) (cat : obj -> obj -> Type)

data LiftedFunctor : Type -> Type where
  Lift : (f : Type -> Type) -> (a : Type) -> LiftedFunctor (f a)

interface (RawCategory r, RawCategory t) => PFunctor (p : robj -> xobj -> tobj) (r : robj -> robj -> Type) (t : tobj -> tobj -> Type) where
  first : r a b -> t (p a c) (p b c)

interface (RawCategory s, RawCategory t) => QFunctor (q : xobj -> sobj -> tobj) (s : sobj -> sobj -> Type) (t : tobj -> tobj -> Type) where
  second : s a b -> t (q c a) (q c b)

--interface (RawCategory a, RawCategory b) => Bifunctor ()


--interface RawGenBifunctor (f : aobj -> bobj -> cobj) (acat : aobj -> aobj -> Type) (bcat : bobj -> bobj -> Type) where


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
