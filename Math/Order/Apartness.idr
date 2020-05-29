import Builtins

data Either a b
  = Left  a
  | Right b

interface Reflexive ty (rel : ty -> ty -> Type) where
  refl : (a : ty) -> a `rel` a

interface Irreflexive ty (rel : ty -> ty -> Type) where
  irrefl : (a : ty) -> a `rel` a -> Void

interface Coreflexive ty (rel : ty -> ty -> Type) (eq : ty -> ty -> Type) where
  corefl : (a, b : ty) -> a `rel` b -> a `eq` b

Dual : (rel : ty -> ty -> Type) -> (ty -> ty -> Type)
Dual rel = flip rel

interface Symmetric ty (rel : ty -> ty -> Type) where
  sym : (a, b : ty) -> a `rel` b -> b `rel` a

interface Antisymmetric ty (rel : ty -> ty -> Type) (eq : ty -> ty -> Type) where
  antisym : (a, b : ty) -> a `rel` b -> b `rel` a -> a `eq` b

interface Transitive ty (rel : ty -> ty -> Type) where
  trans : (a, b, c : ty) -> a `rel` b -> b `rel` c -> a `rel` c

--- Is this a "left" version????
interface Cotransitive ty (rel : ty -> ty -> Type) where
  cotrans : (a, b, c : ty) -> a `rel` b -> Either (a `rel` c) (b `rel` c)

interface (Irreflexive ty rel, Symmetric ty rel, Cotransitive ty rel) => Apartness ty (rel : ty -> ty -> Type) where

interface (Reflexive ty rel, Symmetric ty rel, Transitive ty rel) => Equivalence ty (rel : ty -> ty -> Type) where

(Not (a = b)) => SymmetricRelation Type (b = a) where
  sym x y = ?sym

--(Apartness ty rel -> Void) => Equivalence ty rel where
  --sym x y = ?sym
  --trans x y z = ?trans
