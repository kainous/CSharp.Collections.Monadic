module Math.Categorical.Functor

import Builtins

%default total
%access public export

interface Functor' (f : Type -> Type) where
  map : (func : a -> b) -> f a -> f b

--interface Functor' f => Functor (f : Type -> Type) where
--  preservesIdentity : {a : Type} -> {g : a -> a} -> {x : f a} -> ((v : a) -> g v = v) -> map g x = x
--  preservesComposition : (f : a -> b) -> (g : b -> c) -> f >> g -- map (f << g) = map f << map g
  --preservesComposition : (f : b -> c) -> (g : a -> b) -> f << g -- map (f << g) = map f << map g

infixr 4 <$>

(<$>) : Functor' f => (func : a -> b) -> f a -> f b
(<$>) = map

-- Why does this only apply to the second argument?
--Functor' (Pair a) where
--  map f (x, y) = (x, f y)
