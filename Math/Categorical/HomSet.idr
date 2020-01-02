module Math.Categorical.HomSet

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid
import Math.Categorical.Category
import Math.Categorical.Functor
import Math.Categorical.Applicative

%default total
%access public export

--Morph : Type -> Type -> Type
--Morph a b = Morph (a -> b)


infixr 4 ~>, >>>, >>>>
||| HomSet
public export
data Morphism : Type -> Type -> Type where
  Mor : (a -> b) -> Morphism a b

--public export
--data Endomorphism : Type -> Type where
--  Endo : (a -> a) -> Endomorphism a

public export
(~>) : Type -> Type -> Type
(~>) = Morphism

Magmoid (~>) where
  compose (Mor f) (Mor g) = Mor (f << g)

Point ((~>) a) where
  wrap = const >> Mor

Apply ((~>) a) where
  ap (Mor f) (Mor g) = Mor (\x => f x (g x))

Applicative' ((~>) t) where


--export
--id : (a:Type) -> (a ~> a)
--id a = Mor id


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

rightComposition : {f, g : a -> b} -> {h : b -> c} -> f = g -> f >> h = g >> h
rightComposition Refl = Refl

leftComposition : {f, g : b -> c} -> {h : a -> b} -> f = g -> h >> f = h >> g
leftComposition Refl = Refl

--flipFlip : {f : a -> b -> c} -> f = flip (flip f)
--flipFlip = funext <| \_ => (funext <| \_ => Refl)

export
Semigroupoid' (~>) where

export
Semigroupoid (~>) where
  compositionIsAssociative {f} {g} {h} = unwrappedProof f g h where
    --rtlAssociativityOfFunctions : (f : c -> d) -> (g : b -> c) -> (h : a -> b) -> f << (g << h) = (f << g) << h
    --rtlAssociativityOfFunctions f g h = Refl

    unwrappedProof : (f : c ~> d) -> (g : b ~> c) -> (h : a ~> b) -> f << (g << h) = (f << g) << h
    -- The cong removes the extra {Mor} created after composition
    unwrappedProof (Mor f) (Mor g) (Mor h) = cong <| rtlAssociativityOfFunctions f g h

export
Category' (~>) where
  cid = Mor id

--isIsLeftUnital : (cid : (b ~> b)) -> cid >> x = x

--export
--Category (~>) where
--  idIsLeftUnital {f} = cid `compose` f = f
--  idIsRightUnital = ?rhs2
  --idIsLeftUnital {x} = qed where
--    qed : cid << x = x
    --qed = ?qed_rhs
  --idIsRightUnital = ?rhsr

rightHomComposition : .{f, g : a ~> b} -> .{h : b ~> c} -> f = g -> f >> h = g >> h
rightHomComposition Refl = Refl
