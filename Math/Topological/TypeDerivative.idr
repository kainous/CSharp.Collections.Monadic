module Math.Topological.TypeDerivative

import Builtins

%default total
%access public export

data DerivativeWitness : (f : Type -> Type) -> (df : Type -> Type) -> (x : Type) -> (e : Type) -> Type where
  derivativeWitness : (d : Type) -> (Iso (f (Either x e))) (Either (f x) (Either (e, df x) (e, e) d)))) -> DerivativeWitness f df x e

D : (Type -> Type) -> (Type -> Type) -> Type
D f df = (x : Type) -> (e : Type) -> DerivativeWitness f df x e

data Id a = MkId a

did : D Id (Const ())
