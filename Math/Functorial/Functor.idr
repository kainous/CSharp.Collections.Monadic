module Math.Categorical.Functor

import Builtins

%default total
%access public export

-- Use w to mean "wrapped"
interface Functor' (w : Type -> Type) where
  map : (a -> b) -> w a -> w b

infixr 4 !>, <!, $>, <$

-- We use the notation !> to mean "unwrap, then apply, then wrap"

(<!) : Functor' w => (a -> b) -> w a -> w b
(<!) = map

(!>) : Functor' w => w a -> (a -> b) -> w b
(!>) = flip map

(<$) : Functor' w => a -> w b -> w a
(<$) = map << const

($>) : Functor' w => w a -> b -> w b
($>) = flip (<$)

interface Functor' w => Functor (w : Type -> Type) where
  preservesIdentity    : .{a : Type}   -> .{id : a -> a} -> .{x : w a} -> ((v : a) -> id v = v) -> x !> id = x
  preservesComposition : .{f : a -> b} -> .{g : b -> c}  -> .{x : w a} -> (map (f >> g)) x = (map f >> map g) x


-- Why does this only apply to the second argument?
--Functor' (Pair a) where
--  map f (x, y) = (x, f y)
