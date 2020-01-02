module Math.Categorical.Alternative

import Builtins
import Math.Categorical.Applicative

%default total
%access public export

infixl 3 <|>, <>

interface Semigroup ty where
  plus : ty -> ty -> ty

interface Semigroup m => Reducer c m where
  unitt : c -> m
  append  : m -> c -> m
  prepend : c -> m -> m

  -- This is monoidal>>>???
  -- Look up reducer in snoc cons
  prepend unitt m = m
  append m unitt = m

interface Monoid ty where
  neutral : ty
  (<>) : ty -> ty -> ty

data Alternate f a = Alt f a

interface Applicative' f => Alternative' (f : Type -> Type) where
  empty : f a
  (<|>) : f a -> f a -> f a

Alternative' f => Monoid (Alternate f a) where
  neutral = empty
  (Alt a) <> (Alt b) = Alt (a <|> b)

  --some v : f a -> f [a]
  --some v = some_v where
    --many_v = some_v <|> wrap []
    --some_v = (::) <$> v <*> many_v
  --many : f a -> f [a]
