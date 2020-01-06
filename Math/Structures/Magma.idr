module Magma

import Builtins

infixr 2 ~>
infixl 4 <> --, >>
--infixl 0 <|, |>

data (~>) : Type -> Type -> Type where
  MorM : (a -> b) -> a ~> b

(|>) : a -> (a ~> b) -> b
x |> (MorM f) = f x

(<|) : (a ~> b) -> a -> b
(MorM f) <| x = f x

flipM : (a ~> b ~> c) -> (b ~> a ~> c)
flipM (MorM f) = MorM (\y => MorM(\x => y |> f x))

flipFlip : (fun : a ~> b ~> c) -> fun = flipM (flipM fun)
flipFlip f =
  j where
    j : f = flipM (flipM f)
    j = case (f, flipM (flipM f)) of
        ((MorM f'), (MorM g')) => ?rhss

interface Magma ty where
  constructor MkMagma
  (<>) : ty -> ty -> ty

flip : (f : a -> b -> c) -> b -> a -> c
flip f x y = f y x

--Move this to the level of a Morphism, and you can definitely prove it
--flipFlip : (f : a -> b -> c) -> f = flip (flip f)
--flipFlip f = ?flipFlip_rhs

Opposite : Magma ty -> Magma ty
Opposite (MkMagma f) = MkMagma (Builtins.flip f)

cong : {f : x -> y} -> (a = b) -> (f a = f b)
cong Refl = Refl

interface Magmoid (mor : obj -> obj -> Type) where
  constructor MkMagmoid
  (>>) : mor a b -> mor b c -> mor a c

opOfOpIsPrimal : (m : Magma ty) -> m = Opposite (Opposite m)
--opOfOpIsPrimal = \(MkMagma x) => cong {MkMagma} (?rhsfd)

data Identity ty = Id ty

data Morphism a b = Mor (a -> b)

--Magmoid Morphism where
--  (Mor f) >> (Mor g) = Mor (\x => g (f x))

--Opp : Magmoid arr -> Magmoid arr
--Opp (MkMagmoid f) = MkMagmoid (\g, f' => g >> f')
