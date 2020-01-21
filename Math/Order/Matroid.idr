import Builtins

data Nat = Z | S Nat
-- This is done this way, because an eq is required to define antisymmetric.... HOWEVER, can we define eq here in terms of Partial and prove equivalence of eq instead?
-- How to constrain this eq to be an Equivalence?

data Eq a b = MkEq a b

interface Equivalence obj where
  reflexive : obj -> Eq obj obj
  symmetric : {a, b : obj} -> Eq a b -> Eq b a

interface EquivalenceClass obj where
  eq : (a, b : obj) -> Equivalence a b

interface PartialOrder (eq : obj -> obj -> Type) (rel : obj -> obj -> Type) where
  reflexive : (a : obj) -> rel a a
  antisymmetric : {a, b : obj} -> rel a b -> rel b a -> eq a b
  transitive : {a, b, c : obj} -> rel a b -> rel b c -> rel a c

interface Semilattice ty where
  jeet : ty -> ty -> ty

  associativity : x `jeet` (y `jeet` z) = (x `jeet` y) `jeet` z
  commutativity : x `jeet` y = y `jeet` x
  idempotency   : x `jeet` x = x

interface ExtendedPartialOrder rel => SetWithHull (rel : obj -> obj -> Type) where
  cl : obj -> obj
  extensive  : (x : obj) -> rel x (cl x)
  idempotent : (x : obj) -> cl(cl(x)) `eq` cl(x)
  increasing : {x, y : obj} -> rel x y -> rel (cl x) (cl y)



--interface SetWithHull eq rel => WeakKuratowskiSet (eq : obj -> obj -> Type) (rel : obj -> obj -> Type) where


interface Preclosure (rel : obj -> obj -> Type) where
  cl  : obj -> obj
  bot : obj
  preservationOfNullity : cl(bot) = bot
  extensivity : (x : obj) -> rel x (cl x)
  increasing : {x, y : obj} -> rel x y -> rel (cl x) (cl y)

{-
interface Premetric ty where
  d : ty -> ty -> Num
  nonNegative : 0 <= d x y
  indiscernables1 : d x y = 0 -> x = y
  indiscernables2 : x = y -> d x y = 0
  symmetry : d x y = d y x
  subadditivity : d x y <= d x z + d z y -}

--interface NormedVectorSpace (rel)



--Premetric ty => Preclosure (<=)


--interface KuratowskiSet ty where
--  cl : ty -> ty
--  kuratowskiAxiom : {a, b : ty} -> (a `join` cl (a)) `join` (cl (cl B)) = cl(a `meet` b) `without` cl(bot)
