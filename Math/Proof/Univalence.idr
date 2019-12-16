module Univalence

import Builtins

%default total

data IdPath : a -> a -> Type where
  Refl : IdPath x x

J : {a : Type} -> (m : (x,y : a) -> IdPath x y -> Type)
               -> (e : (x : a) -> m x x Refl)
               -> (x,y : a) -> (p : IdPath x y) -> m x y p
J m e x x Refl = e x

isSingleton : Type -> Type
isSingleton a = (x : a ** (y : a) -> IdPath x y)

fiber : (a -> b) -> b -> Type
fiber {a} f y = (x : a ** IdPath (f x) y)

isEquiv : (a -> b) -> Type
isEquiv {b} f = (y : b) -> isSingleton (fiber f y)

Eq : (a,b : Type) -> Type
Eq a b = (f : (a -> b) ** isEquiv f)

singletonType : a -> Type
singletonType {a} x = (y : a ** IdPath y x)

eta : (x : a) -> singletonType x
eta x = (x ** Refl)

singletonProof : (x : a) -> isSingleton (singletonType x)
singletonProof {a} x = (eta x ** g x) where
    m : (y,x : a) -> Id y x -> Type
    m y x p = Id (eta x) (y ** p)

    phi : (y,x : a) -> (p : IdPath y x) -> IdPath (eta x) (y ** p)
    phi y x p = J m (\x => Refl) y x p

    g : (x : a) -> (s : singletonType x) -> IdPath (eta x) s
    g x (y ** p) = phi y x p

idIsEquiv : {a : Type} -> isEquiv (id {a = a})
idIsEquiv = singletonProof

IdToEq : (a,b : Type) -> IdPath a b -> Eq a b
IdToEq a b = J (\a,b,p => Eq a b) (\a => (id ** idIsEquiv)) a b

IsUnivalent : Type
IsUnivalent = (a,b : Type) -> isEquiv (IdToEq a b)

postulate univalence : IsUnivalent
