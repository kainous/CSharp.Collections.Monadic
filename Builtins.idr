%unqualified

%access public export
%default total

namespace Builtins
  id : a -> a
  id x = x

  the : (a : Type) -> (value : a) -> a
  the _ = id

  const : a -> b -> a
  const x _ = x

  flip : (a -> b -> c) -> (b -> a -> c)
  flip f x y = f y x

  subst : {A : Type} -> {a, a' : A} -> (P : A -> Type) -> a = a' -> P a -> P a'
  subst p Refl x = x

  coerce : {A, B : Type} -> A = B -> A -> B
  coerce = subst id

  cong : .{f : t -> u} -> a = b -> f a = f b
  cong Refl = Refl

  uncong : .{f, g : t -> u} -> f = g -> f x = g x
  uncong Refl = Refl

  ||| The canonical single-element type, also known as
  ||| the trivially true proposition.
  data Unit =
    ||| The trivial constructor for `()`.
    MkUnit

  interface Magmoid (mor : obj -> obj -> Type) where
    lcompose : a `mor` b -> b `mor` c -> a `mor` c
    rcompose : b `mor` c -> a `mor` b -> a `mor` c

    lcompose = flip rcompose
    rcompose = flip lcompose

  interface Magmoid mor => Semigroupoid (mor : obj -> obj -> Type) where
    associative : .{f : a `mor` b} -> .{g : b `mor` c} -> .{h : c `mor` d} -> f `lcompose` (g `lcompose` h) = (f `lcompose` g) `lcompose` h

  infixr 14 >>, <<

  (>>) : Semigroupoid mor => a `mor` b -> b `mor` c -> a `mor` c
  (>>) = lcompose

  (<<) : Semigroupoid mor => b `mor` c -> a `mor` b -> a `mor` c
  (<<) = rcompose

  interface Magmoid mor => UnitalMagmoid (mor : obj -> obj -> Type) where
    ident : a `mor` a
    leftIdent  : (f : a `mor` b) -> ident `lcompose` f = f
    rightIdent : (f : a `mor` b) -> f `lcompose` ident = f

  interface (UnitalMagmoid mor, Semigroupoid mor) => Category (mor : obj -> obj -> Type) where

  infixl 4 ~>

  data (~>) a b = Mor (a -> b)

  Magmoid (~>) where
    lcompose (Mor f) (Mor g) = Mor (\x => g (f x))
    rcompose (Mor f) (Mor g) = Mor (\x => f (g x))
  UnitalMagmoid (~>) where
    ident = Mor id
    leftIdent (Mor f) = cong ?rhs_1

  -- 4 meanings of identity
  -- * id function
  -- * Identity monad
  -- * Id as the equality type
  -- * id on a category / such as an identity relation

  --interface BicartesianClosedCategory (mor : obj -> obj -> Type) where
--    exponentiation : a -> b ->

  ||| The type of pairs of types
  data Pair : (A, B : Type) -> Type where
    ||| The constructor for a pair of objects
    MkPair : {A, B : Type} -> (a : A) -> (b : B) -> Pair A B

  data DPair : (a : Type) -> (P : a -> Type) -> Type where
    MkDPair : .{P : a -> Type} -> (x : a) -> (pf : P x) -> DPair a P

  ||| The empty type, also known as the trivially false proposition.
  |||
  ||| Use `void` or `absurd` to prove anything if you have a variable of type `Void` in scope.
  data Void : Type where
  ||| The eliminator for the `Void` type.
  void : Void -> a

  Not : Type -> Type
  Not a = a -> Void

  interface Uninhabited t where
    total uninhabited : t -> Void

  Uninhabited Void where
    uninhabited a = a

  absurd : Uninhabited t => (h : t) -> a
  absurd h = void (uninhabited h)

  -- Id differs from the (=) type where (=) takes 'a' and 'b', but Id requires both types be the same
  infixl 4 ==, ~=~
  --data IdPath : a -> a -> Type where
  --  Refl : IdPath x x

  --data Eq a = Refl a a

  interface PreorderRelation (ty : Type) (rel : ty -> ty -> Type) where
    refl  : .{a : ty} -> a `rel` a
    trans : .{a, b, c : ty} -> a `rel` b -> b `rel` c -> a `rel` c

  interface SymmetricRelation (ty : Type) (rel : ty -> ty -> Type) where
    sym : .{a, b : ty} -> a `rel` b -> b `rel` a

  interface (PreorderRelation ty rel, SymmetricRelation ty rel) => EquivalenceRelation (ty : Type) (rel : ty -> ty -> Type) where

  --data Dec : Type -> Type where
  --  Yes : (prf    :     prop) -> Dec prop
  --  No  : (contra : Not prop) -> Dec prop

  PreorderRelation Type (=) where
    refl = Refl
    trans Refl Refl = Refl
  SymmetricRelation Type (=) where
    sym Refl = Refl

  EquivalenceRelation Type (=) where

  infixl 0  |>, <|, ||>, <||

  -- can this be replaced with the HomSet version?
  (|>) : a -> (a -> b) -> b
  x |> f = f x
  -- can this be replaced with the HomSet version?
  (<|) : (a -> b) -> a -> b
  f <| x = f x

  (||>) : (a, b) -> (a -> b -> c) -> c
  (x, y) ||> f = f x y

  (<||) : (a -> b -> c) -> (a, b) -> c
  f <|| (x, y) = f x y

  -- Note that the pipe application operations here should also be used for the following
  -- Consider what the following mean for each : composition, products, coproducts
  -- * SortedMap / HashMap
  -- ** Composite dictionaries can be created this way
  -- ** Dictionaries using Pair works this way too
  -- ** Aren't these actually Dependent Pairs??????
  -- * Applications of type m a -> m (a -> b) -> m b |||| i.e. lifted application
  -- ** Dictionaries
  -- * Applications of type (a -> m b)


  -- can this be replaced with the Semigroupoid version?
  {-(>>) : (a -> b) -> (b -> c) -> a -> c
  f >> g = \x => g (f x)

  -- can this be replaced with the Semigroupoid version?
  (<<) : (b -> c) -> (a -> b) -> a -> c
  g << f = \x => g (f x)

  data Apartness : (a : ty) -> (b:ty) -> Type where
    MkApartness : (x:ty) -> (y:ty) -> (prf : Not (x = y)) -> Apartness x y

  --SymmetricRelation Type (Apartness prf) where
  --  sym prf = ?rhs

  ltrAssociativityOfFunctions : (f : a -> b) -> (g : b -> c) -> (h : c -> d) -> f >> (g >> h) = (f >> g) >> h
  ltrAssociativityOfFunctions f g h = Refl

  rtlAssociativityOfFunctions : (f : c -> d) -> (g : b -> c) -> (h : a -> b) -> f << (g << h) = (f << g) << h
  rtlAssociativityOfFunctions f g h = Refl

  uncurry : (a -> b -> c) -> (a, b) -> c
  uncurry = (<||)

  curry : (Pair a b -> c) -> a -> b -> c
  curry f a b = f (a, b)

  cong : .{f : t -> u} -> a = b -> f a = f b
  cong Refl = Refl

  uncong : {f, g : t -> u} -> f = g -> f x = g x
  uncong Refl = Refl -}

  ||| Assert to the totality checker that y is always structurally smaller than
  ||| x (which is typically a pattern argument, and *must* be in normal form
  ||| for this to work)
  ||| @ x the larger value (typically a pattern argument)
  ||| @ y the smaller value (typically an argument to a recursive call)
  assert_smaller : (x : a) -> (y : b) -> b
  assert_smaller x y = y

  ||| Assert to the totality checker that the given expression will always
  ||| terminate.
  assert_total : a -> a
  assert_total x = x

  ||| Assert to the totality checker that the case using this expression
  ||| is unreachable
  assert_unreachable : a
  -- compiled as primitive

  ||| Abort immediately with an error message
  idris_crash : (msg : String) -> a
  -- compiled as primitive

  ||| Perform substitution in a term according to some equality.
  replace : {a:_} -> {x:_} -> {y:_} -> {P : a -> Type} -> x = y -> P x -> P y
  replace Refl prf = prf

  ||| Perform substitution in a term according to some equality.
  |||
  ||| Like `replace`, but with an explicit predicate, and applying the rewrite
  ||| in the other direction, which puts it in a form usable by the `rewrite`
  ||| tactic and term.
  rewrite__impl : (P : a -> Type) -> x = y -> P y -> P x
  rewrite__impl p Refl prf = prf

  %used idris_crash msg

  ||| Subvert the type checker. This function is abstract, so it will not reduce in
  ||| the type checker. Use it with care - it can result in segfaults or worse!
  export
  believe_me : a -> b
  believe_me x = assert_total (prim__believe_me _ _ x)

  postulate
  funext : {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

  funext2 : {f, g : a -> b -> c} -> ((x : a) -> (y : b) -> f x y = g x y) -> f = g
  funext2 h = funext (\x => funext (\y => h x y))

  funext3 : {f, g : a -> b -> c -> d} -> ((x : a) -> (y : b) -> (z : c) -> f x y z = g x y z) -> f = g
  funext3 h = funext (\x => funext (\y => funext (\z => h x y z)))

  --flipOfFlip : Builtins.flip >> Builtins.flip = Builtins.id
  --flipOfFlip = funext3 (\f, x, y => Refl)


  idPoint : id x = x
  --funext x = assert_total (prim__believe_me _ _ x)
  idPoint = Refl

  abstractionApplication : {f : a -> b} -> f x = y -> (\z => f z) x = y
  abstractionApplication Refl = Refl

  compositionOfAbstraction : {f : (a -> b) -> c} -> f = (\g => f (\x => g x))
  compositionOfAbstraction = funext $ \g => Refl

  ||| Subvert the type checker. This function *will*  reduce in the type checker.
  ||| Use it with extreme care - it can result in segfaults or worse!
  public export
  really_believe_me : a -> b
  really_believe_me x = assert_total (prim__believe_me _ _ x)

  -- Pointers as external primitive; there's no literals for these, so no
  -- need for them to be part of the compiler.

  export data Ptr : Type
  export data ManagedPtr : Type
  export data CData : Type

  %extern prim__readFile : prim__WorldType -> Ptr -> String
  %extern prim__readChars : prim__WorldType -> Int -> Ptr -> String
  %extern prim__writeFile : prim__WorldType -> Ptr -> String -> Int

  %extern prim__vm : prim__WorldType -> Ptr
  %extern prim__stdin : Ptr
  %extern prim__stdout : Ptr
  %extern prim__stderr : Ptr

  %extern prim__null : Ptr
  %extern prim__managedNull : ManagedPtr
  %extern prim__eqPtr : Ptr -> Ptr -> Int
  %extern prim__eqManagedPtr : ManagedPtr -> ManagedPtr -> Int
  %extern prim__registerPtr : Ptr -> Int -> ManagedPtr

  -- primitives for accessing memory.
  %extern prim__asPtr : ManagedPtr -> Ptr
  %extern prim__sizeofPtr : Int
  %extern prim__ptrOffset : Ptr -> Int -> Ptr
  %extern prim__peek8 : prim__WorldType -> Ptr -> Int -> Bits8
  %extern prim__peek16 : prim__WorldType -> Ptr -> Int -> Bits16
  %extern prim__peek32 : prim__WorldType -> Ptr -> Int -> Bits32
  %extern prim__peek64 : prim__WorldType -> Ptr -> Int -> Bits64

  %extern prim__poke8 : prim__WorldType -> Ptr -> Int -> Bits8 -> Int
  %extern prim__poke16 : prim__WorldType -> Ptr -> Int -> Bits16 -> Int
  %extern prim__poke32 : prim__WorldType -> Ptr -> Int -> Bits32 -> Int
  %extern prim__poke64 : prim__WorldType -> Ptr -> Int -> Bits64 -> Int

  %extern prim__peekPtr : prim__WorldType -> Ptr -> Int -> Ptr
  %extern prim__pokePtr : prim__WorldType -> Ptr -> Int -> Ptr -> Int

  %extern prim__peekDouble : prim__WorldType -> Ptr -> Int -> Double
  %extern prim__pokeDouble : prim__WorldType -> Ptr -> Int -> Double -> Int
  %extern prim__peekSingle : prim__WorldType -> Ptr -> Int -> Double
  %extern prim__pokeSingle : prim__WorldType -> Ptr -> Int -> Double -> Int
