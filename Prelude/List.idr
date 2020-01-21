import Builtins
import Prelude.Lazy
import Math.Topological.Pointed
import Math.Functorial.Applicable
import Math.Functorial.ApplicativeFunctor
import Math.Functorial.Bindable
import Math.Functorial.Functor
import Math.Functorial.Monad

--data ListF a x = Nil | Cons a x

--data Nu f = NuF a (a -> f)

infixr 6 ::

-- Lazy is understood by codata
codata Stream : Type -> Type where
  MoreStream : (value : elem) -> Stream elem -> Stream elem

data List ty
  = Stop
  | More ty (List ty)

Pointed List where
  wrap a = More a Stop

concat : List ty -> List ty -> List ty
concat  Stop y = y
concat (More x z) y = More x (concat z y) -- This is what makes lists decidable, but slow

foldr : List ty -> (ty -> ty -> ty) -> ty -> ty
foldr  Stop _ y       = y
foldr (More x xs) f y = f x (foldr xs f y)

join : List (List ty) -> List ty
join xss = foldr xss concat Stop

RawFunctor List where
  map _  Stop       = Stop
  map f (More x xs) = More (f x) (map f xs)

Bindable List where
  bind f xs = join (map f xs)

Applicable List where
  ap Stop Stop = Stop
  ap Stop _    = Stop
  ap _ Stop    = Stop
  ap (More f fs) (More x xs) = More (f x) (ap fs xs)

RawApplicativeFunctor List where

--RawMonad List where
  --merge = join
