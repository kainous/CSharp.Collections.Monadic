module Math.Categorical.Monad

import Builtins
import Math.Categorical.Functor
import Math.Categorical.Applicative

%default total
%access public export

interface Bind (f : Type -> Type) where
  bind : (a -> f b) -> f a -> f b

infixl 1 =<<, >>=

(=<<) : Bind f => (a -> f b) -> f a -> f b
(=<<) = bind

(>>=) : Bind f => f a -> (a -> f b) -> f b
(>>=) = flip bind

interface (Bind f, Applicative' f) => Monad' (f : Type -> Type) where

join : Monad' f => f (f a) -> f a
join x = x >>= id

-- join << map join = join << join
-- join << (map (map f)) = map f << join
-- join << map (wrap) = join << wrap = id

--Need monad instance to implement flip, which requires Join
flip : Monad' m => m (a -> b -> c) -> m (b -> a -> c)
flip f = join (wrap (wrap (\y, x => extract (wrap y |> ((wrap x) |> f)))))

{-flip f = join qed where
  qed : m (m c)

  g : m c
  g =
    let r = \x => (x |> f) in
    ?rhs

  --join (wrap (\y, x => ?rhs))
  qed = wrap g-}
