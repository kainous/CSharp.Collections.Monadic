module Math.Categorical.Magmoid

import Builtins

%default total
%access public export

interface Magmoid (p : obj -> obj -> Type) where
  constructor MkMagmoid
  compose : (f : p b c) -> (g : p a b) -> p a c

--record Dual (k : b -> a) a b where
--  constructor MkDual
    --runDual : k b a

--Dual : Magmoid -> Type
--  Dual (MkCompositor comp) = MkCompositor (flip comp)

--Magmoid Morphism where
--  compose (Mor f) (Mor g) = Mor (f << g)

-- p a b -> p b c ->

--flipAp : (a ~> b ~> c) -> (b ~> a ~> c)
--flipAp (Mor f) = Mor (\x => Mor(\y => let (Mor g) = f y in g x))

--data Dual : (obj -> obj -> Type) -> Type where
--  MkDual : (k : obj -> obj -> Type) -> Dual k

--[dual]
--Dual k => Magmoid k where
--  compose = ?rhs




--dd : Magmoid p => p = dual (dual p)
--dd = ?dd_rhs
