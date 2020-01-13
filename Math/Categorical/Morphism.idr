module Math.Categorical.HomSet

import Builtins
import Math.Categorical.Magmoid
import Math.Categorical.Semigroupoid
--import Math.Categorical.Category
import Math.Functorial.Functor
import Math.Functorial.Applicable
import Math.Functorial.ApplicativeFunctor
import Math.Topological.Pointed

%default total
%access public export

data Morphism a b = Mor (a -> b)

infixr 4 ~>
(~>) : Type -> Type -> Type
(~>) = Morphism

data Endomorphism = Endo (a -> a)

Pointed ((~>) a) where
  wrap = const >> Mor

Applicable ((~>) a) where
  ap (Mor f) (Mor g) = Mor (\x => f x (g x))

RawApplicativeFunctor ((~>) t) where

ApplicativeFunctor ((~>) t) where
  applicativeIdentity (Mor f) = Refl
  applicativeComposition (Mor x) (Mor f) (Mor g) = Refl
  applicativeInterchange x (Mor f) = Refl
  homomorphism f x = cong (unwrapped f x) where
    unwrapped : (f : a -> b) -> (x : a) -> (\_ => f x) = const (f x)
    unwrapped f x = funext (\_ => Refl)


Magmoid (~>) where
  compose (Mor f) (Mor g) = Mor (f >> g)

--RawSemigroupoid (~>) where
--  compositionIsAssociative = ?rhs

{-Cast (Endomorphism a) (Morphism a a) where
  cast (Endo f) = Mor f

Cast (Morphism a a) (Endomorphism a) where
  cast (Mor f) = Endo f-}

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
{-
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
rightHomComposition Refl = Refl -}


{-

Notions
Univalence


Equality Type : Built in type
Preorder : an interface with relation qualities
Category : an interface with algebraic qualities
•	(happens to be a preorder + algebraic laws on id)
Equivalence : an interface with preorder qualities
Congruence : an interface with equivalence qualities
Morphism : an interface maintaining a source and target of type obj (i.e. within category)
Pair : a 0-level morphism with source and target identified by left and right elements
Hom : (is the “internal hom”) a function wrapped into a morphism for use (implements ‘HomSet’) [difference between a → (b → Type) and (a → b) → Type]; source and target are likely Types
HomSet : an interface, from morphism and applicative, with the notion of having products, etc. (exists on a closed category)
Cast : a lossy hom of type Type, possibly considered part of an adjoint (why different from Hom??)
Isomorphism : a bidirectional pair of homs, also (implements adjunction ?? proving unit and counit)
Equivalence : an isomorphism and preorder with algebraic proof of 2 ids. This is something that can be shown to be univalent

1 External Hom is acquired by using Profunctor on id.




-}
