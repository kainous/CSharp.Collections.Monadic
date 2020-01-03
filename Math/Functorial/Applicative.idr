module Math.Functorial.Applicative

import Builtins
import Math.Topological.Pointed
import Math.Functorial.Applicable
import Math.Functorial.Functor
import Math.Categorical.Magmoid

%default total
%access public export

-- Do we really want functor here yet?
interface (Pointed w, Applicable w) => Applicative' (w : Type -> Type) where
  --wrap2 : Applicative' w => (a -> b -> c) -> w a -> w b -> w c
  --wrap2 f x y = ap (f <! x) y

  --(*>) : w a -> w b -> w b
  --u *> v = (id <! u)

(<|) : Applicative' f => f (a -> b) -> f a -> f b
(<|) = ap

(|>) : Applicative' f => f a -> f (a -> b) -> f b
(|>) = flip ap

Applicative' w => Functor' w where
  map f x = x |> wrap f

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
(>>>) : Applicative' w => w (a -> b) -> w (b -> c) -> w (a -> c)
f >>> g = g |> (f |> wrap (>>))

(<<<) : Applicative' w => w (b -> c) -> w (a -> b) -> w (a -> c)
(<<<) = flip (>>>)

interface (Applicative' w) => Applicative (w : Type -> Type) where
  -- This is not necessary, because map is defined this way.
  --applicativeMap : (x : w a) -> (g : a -> b) -> x !> g = x |> wrap g
  applicativeIdentity : {x : w a} -> x |> wrap id = x
  applicativeComposition : {x : w a} -> {f : w (a -> b)} -> {g : w (b -> c)} -> x |> (f >>> g) = (x |> f) |> g
  applicativeInterchange : {x : a} -> {f : w (a -> b)} -> wrap x |> f = f |> wrap (\g : (a -> b) => g x)
  homomorphism : {f : a -> b} -> {x : a} -> ap {f=w} (wrap f) (wrap x) = wrap (f x)
