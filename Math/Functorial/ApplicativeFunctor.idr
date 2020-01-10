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
interface (Pointed w, Applicable w) => RawApplicativeFunctor (w : Type -> Type) where

RawApplicativeFunctor w => RawFunctor w where
  map = wrap >> ap

record FunctorMorphism (w : Type -> Type) a b where
  constructor FunctMorph
  applyFunctMorph : w (a -> b)

infixl 3 >>>, <<<
(>>>) : RawApplicativeFunctor w => w (a -> b) -> w (b -> c) -> w (a -> c)
f >>> g = g |> (f |> wrap (>>))

--Applicable w => Applicable (FunctorMorphism w a) where
  --ap (FunctMorph f) (FunctMorph x) = ap f x

--data Endomorphism a = Endo (a -> a)

RawApplicativeFunctor w => Magmoid (FunctorMorphism w) where
  compose (FunctMorph f) (FunctMorph g) = FunctMorph (g |> (f !> (>>)))

data Ident a = Id a

Applicable Ident where
  ap (Id f) (Id x) = Id (f x)

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
