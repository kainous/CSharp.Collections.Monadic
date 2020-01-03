module Math.Categorical.Magmoid

import Builtins

%default total
%access public export

interface Magmoid (p : obj -> obj -> Type) where
  constructor MkMagmoid
  compose : (f : p b c) -> (g : p a b) -> p a c

reverseCompose : Magmoid p => (f : p a b) -> (g : p b c) -> p a c
reverseCompose f g = compose g f

data Dual : {obj : Type} -> (obj -> obj -> Type) -> (obj -> obj -> Type) where
  MkDual : (mor : obj -> obj -> Type) -> (a : obj) -> (b : obj) -> Dual mor b a


--record Dual (k : Type -> Type -> Type) where
--  constructor MkDual
--  runDual : k b a

--dualize : Magmoid mor -> Dual (Magmoid)
--dualize (MkMagmoid compose) =

--Magmoid (flip mor) => Magmoid (Dual mor) where
--  compose (MkDual mor c b) (MkDual mor b a) = qed where
    --qed : Dual mor a c
    --qed =
--      let x0 = flip (compose {p=flip mor}) in
      --let x1 = MkDual x0 in
  --    ?rhs
--dual : Magmoid mor -> Dual mor

--Magmoid mor => Dual mor where

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
