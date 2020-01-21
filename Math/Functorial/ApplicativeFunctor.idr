module Math.Functorial.ApplicativeFunctor

import Builtins
import Math.Topological.Pointed
import Math.Functorial.Applicable
import Math.Functorial.Functor
import Math.Categorical.Magmoid
import Math.Algebraic.Magma

%default total
%access public export

-- Do we really want functor here yet?
interface (Pointed w, Applicable w, RawFunctor w) => RawApplicativeFunctor (w : Type -> Type) where
  RawFunctor w where
    map = wrap >> ap

-- This structure forms the F-algebra
record FunctorMorphism (w : Type -> Type) a b where
  constructor FunctMorph
  applyFunctMorph : w (a -> b)

infixl 3 >>>, <<<
(>>>) : RawApplicativeFunctor w => w (a -> b) -> w (b -> c) -> w (a -> c)
f >>> g = g |> (f |> wrap (>>))

RawApplicativeFunctor w => Magmoid (FunctorMorphism w) where
  compose (FunctMorph f) (FunctMorph g) = FunctMorph (g |> (f !> (>>)))

data Ident a = Id a

Applicable Ident where
  ap (Id f) (Id x) = Id (f x)

RawFunctor Ident where


data B = T | F

--syntax "[%" [f] [x] "%]" = f <! x

--or : B -> B -> B
--or T _ = T
--or F x = x

--not : B -> B
--not T = F
--not F = T

--test1 : Ident B
--test1 = Id T

--test2 : Ident B
--test2 = Id F

--test0 : Ident B
--test0 = [% or test1 test2 %]

Pointed Ident where
  wrap = Id

RawApplicativeFunctor Ident where

  --infixl 3 >>>, <<<
  {-(>>>) : RawApplicativeFunctor w => w (a -> b) -> w (b -> c) -> w (a -> c)
  f >>> g = g |> (f |> wrap (>>))

  (<<<) : RawApplicativeFunctor w => w (b -> c) -> w (a -> b) -> w (a -> c)
  (<<<) = flip (>>>) -}

interface (RawApplicativeFunctor w) => ApplicativeFunctor (w : Type -> Type) where
  -- This is not necessary, because map is defined this way.
  --applicativeMap : (x : w a) -> (g : a -> b) -> x !> g = x |> wrap g
  applicativeIdentity : (x : w a) -> x |> wrap Builtins.id = x
  applicativeComposition : (x : w a) -> (f : w (a -> b)) -> (g : w (b -> c)) -> x |> (f >>> g) = (x |> f) |> g
  applicativeInterchange : (x : a) -> (f : w (a -> b)) -> wrap x |> f = f |> wrap (\g : (a -> b) => g x)
  homomorphism : (f : a -> b) -> (x : a) -> ap {f=w} (wrap f) (wrap x) = wrap (f x)

--rhs2 : ApplicativeFunctor w => (x : w a) -> (f : a -> b) -> (g : b -> c) -> ap (wrap (\x1 => g (f x1))) x = ap (wrap g) (ap (wrap f) x)
--rhs2 x f g = ?rhs2_rhs

--ApplicativeFunctor w => Functor w where
--  preservesIdentity x  = applicativeIdentity x
--  preservesComposition {f} {g} x = rhs2 x f g



  --wrap2 : Applicative' w => (a -> b -> c) -> w a -> w b -> w c
  --wrap2 f x y = ap (f <! x) y

  --(*>) : w a -> w b -> w b
  --u *> v = (id <! u)

--Applicative' w => Functor' w where
--  map f x = x |> wrap f

----------------------------------------------- Arrrows?

--Applicative' w => Magmoid w where
{-
interface Category (mor : obj -> obj -> Type) where
  id : mor a a
  comp : mor a b -> mor b c -> mor a c

infixr 5 <++>
infixr 3 ***, &&&
infixr 2 +++, \|/

data Morphism a b = Mor (a -> b)

interface Category mor => Arrow (mor : Type -> Type -> Type) where
  arrow : (a -> b) -> mor a b
  first : {a, b, c : Type} -> mor a b -> mor (Pair a c) (Pair b c)

  --(***) : mor a b -> mor a' b' -> mor (a, a') (b, b')

Category Morphism where
  id = Mor (\x => x)
  comp (Mor f) (Mor g) = Mor (f >> g)

Arrow Morphism where
  arrow f = Mor f
  first (Mor f) = Mor <| \(a, b) => (f a, b)



Applicative' w => Category (w) where -}


----------------------------------------------- Arrrows?


-- Category here... Should >> and << be allowed
infixl 3 >>>, <<<
{-(>>>) : RawApplicativeFunctor w => w (a -> b) -> w (b -> c) -> w (a -> c)
f >>> g = g |> (f |> wrap (>>))

(<<<) : RawApplicativeFunctor w => w (b -> c) -> w (a -> b) -> w (a -> c)
(<<<) = flip (>>>)

interface (RawApplicativeFunctor w) => ApplicativeFunctor (w : Type -> Type) where
  -- This is not necessary, because map is defined this way.
  --applicativeMap : (x : w a) -> (g : a -> b) -> x !> g = x |> wrap g
  applicativeIdentity : {x : w a} -> x |> wrap id = x
  applicativeComposition : {x : w a} -> {f : w (a -> b)} -> {g : w (b -> c)} -> x |> (f >>> g) = (x |> f) |> g
  applicativeInterchange : {x : a} -> {f : w (a -> b)} -> wrap x |> f = f |> wrap (\g : (a -> b) => g x)
  homomorphism : {f : a -> b} -> {x : a} -> ap {f=w} (wrap f) (wrap x) = wrap (f x)
-}
