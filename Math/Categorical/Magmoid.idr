module Math.Categorical.Magmoid

import Builtins

%default total
%access public export

namespace Categorical

  interface Magmoid (p : obj -> obj -> Type) where
    constructor MkMagmoid
    -- This version of compose is opposite (flipped) from the usual notion of compose
    compose : (f : p a b) -> (g : p b c) -> p a c

  reverseCompose : Magmoid p => (f : p b c) -> (g : p a b) -> p a c
  reverseCompose f g = compose g f

  data Dual : {obj : Type} -> (obj -> obj -> Type) -> (obj -> obj -> Type) where
    MkDual : (mor : obj -> obj -> Type) -> (a : obj) -> (b : obj) -> Dual mor b a

  -- This is almost like sym
  commutation : Magmoid mor => mor a b -> mor b a -> (mor a a, mor b b)
  commutation f g = (f `compose` g, g `compose` f)

  associatiation : Magmoid mor => mor a b -> mor b c -> mor c d -> (mor a d, mor a d)
  associatiation f g h = (f `compose` (g `compose` h), (f `compose` g) `compose` h)

  --record Epimorph a b where
  --  morph : a -> b
  --  epi   : {g1, g2 : b -> c} -> morph >> g1 = morph g2 -> g1 = g2

  commutator : Magmoid mor => mor a b -> mor b a -> (mor a a -> mor c c) -> (mor b b -> mor c c) -> mor c c = mor c c -> mor a a = mor b b
  commutator x y f g Refl =
    --let z1 = funext (\r => f x = g y) in
    let (s1, s2) = commutation x y in
    let (s3, s4) = (f s1, g s2) in
    ?commutator_rhs


  --record Dual (k : Type -> Type -> Type) where
  --  constructor MkDual
  --  runDual : k b a


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
