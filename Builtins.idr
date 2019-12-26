%unqualified

%access public export
%default total

||| The canonical single-element type, also known as
||| the trivially true proposition.
data Unit =
 ||| The trivial constructor for `()`.
 MkUnit

namespace Builtins
  id : a -> a
  id x = x

  the : (a : Type) -> (value : a) -> a
  the _ = id

  ||| Id differs from the (=) type where (=) takes 'a' and 'b', but Id requires both types be the same
  data IdPath : a -> a -> Type where
    Refl : IdPath x x

  data Pair : a -> b -> Type where
    MkPair : a -> b -> Pair a b

  data DPair : (a : Type) -> (P : a -> Type) -> Type where
    MkDPair : .{P : a -> Type} -> (x : a) -> (pf : P x) -> DPair a P

  --data Eq a = Refl a a

  const : a -> b -> a
  const x _ = x

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

  sym : {left:a} -> {right:b} -> left = right -> right = left
  sym Refl = Refl

  trans : {a:x} -> {b:y} -> {c:z} -> a = b -> b = c -> a = c
  trans Refl Refl = Refl


  infixr 14 >>, <<
  infixr 0  |>, <|

  -- can this be replaced with the HomSet version?
  (|>) : a -> (a -> b) -> b
  x |> f = f x
  -- can this be replaced with the HomSet version?
  (<|) : (a -> b) -> a -> b
  f <| x = f x

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
  (>>) : (a -> b) -> (b -> c) -> a -> c
  f >> g = \x => g (f x)

  -- can this be replaced with the Semigroupoid version?
  (<<) : (b -> c) -> (a -> b) -> a -> c
  g << f = \x => g (f x)

  uncurry : (a -> b -> c) -> Pair a b -> c
  uncurry f (a, b) = f a b

  curry : (Pair a b -> c) -> a -> b -> c
  curry f a b = f (a, b)

  cong : {f : t -> u} -> (a = b) -> (f a = f b)
  cong Refl = Refl

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

  %used idris_crash msg

  ||| Subvert the type checker. This function is abstract, so it will not reduce in
  ||| the type checker. Use it with care - it can result in segfaults or worse!
  export
  believe_me : a -> b
  believe_me x = assert_total (prim__believe_me _ _ x)

  postulate
  funext : {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g
  --funext x = assert_total (prim__believe_me _ _ x)

  theorem : {f : (a -> b) -> c} -> f = (\g => f (\x => g x))
  theorem = funext $ \g => Refl

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
