module Math.Functorial.Functor

import Builtins

%default total
%access public export

-- Use w to mean "wrapped"
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
    --  proofs easier
    (x : w a) ->
    (map (f >> g)) x = (map f >> map g) x


-- Why does this only apply to the second argument?
--Functor' (Pair a) where
--  map f (x, y) = (x, f y)
