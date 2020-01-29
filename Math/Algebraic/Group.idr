--interface Quasigroupoid (arr : obj -> obj -> Type) where
--  qccomp : arr b c -> arr a b -> arr a c
  -- no proof of associativity, because we may not be associative
--  leftDiv : (f : arr a c) -> (g : arr a b) -> arr b c
--  leftDivIdentity : y = x `qccomp` (x `leftDiv` y)
  -- (f : arr b c) -> (g : arr a b) -> g = f `qccomp` (x `leftDiv` y)
  -- (f : arr b c) -> (g : arr a b) -> arr a b = (arr b c) `qccomp` ((arr b c) `leftDiv` (arr a b))
  -- (f : arr b c) -> (g : arr a b) -> arr a b = (arr b c) `qccomp` ((arr b c) `leftDiv` (arr a b))
  -- (f : arr b c) -> (g : arr a b) -> arr a b = (arr b c) `qccomp` (arr a b)

-- Does the nerve of a quasicategory end up creating the dual of the original category?
--

-- if we have a left inverse fst and a right inverse snd
-- We show here that ((a, (b, c)), fst ((a, b), c))) -> ((a, (b, c)), (a, b)) and hence tupling is not associative.
-- A heterogeneous list; however,


interface Category (arr : obj -> obj -> Type) where
  id : arr a a
  comp : arr b c -> arr a b -> arr a c

--commutator only works for isomorphisms / groupoids
--catCommutator : Category arr => (arr a b) -> (arr b a) -> arr a a
--catCommutator f g

--catAssociator : (arr a d) -> (x : arr a b) -> (y : arr b c) -> (z : arr c d)
--catAssociator f

interface Quasigroup ty where
  qproduct : ty -> ty -> ty
  leftDivide  : ty -> ty -> ty
  rightDivide : ty -> ty -> ty

  leftDivideIdentity : y = x `qproduct` (x `leftDivide` y)

--interface Loop

qgAssociator : Quasigroup ty => ty -> ty -> ty -> ty
qgAssociator a b c = (a `qproduct` (b `qproduct` c)) `leftDivide` ((a `qproduct` b) `qproduct` c)
-- if we have a left inverse fst and a right inverse snd
-- We show here that ((a, (b, c)), fst ((a, b), c))) -> ((a, (b, c)), (a, b)) and hence tupling is not associative.
-- A heterogeneous list; however,

interface Group ty where
  product  : ty -> ty -> ty
  inverse  : ty -> ty
  identity : ty

conjugateBy : Group ty => ty -> ty -> ty
conjugateBy x y = (y `product` x) `product` (inverse y)

commutator : Group ty => ty -> ty -> ty
commutator x y = (conjugateBy y x) `product` (inverse y)

interface Group ty => AbelianGroup ty where
  commutative : commutator {ty} x y = identity

interface Monoid ty => AdditiveMonoid ty where
-- Isn't this better defined categorically?
sum : AdditiveMonoid ty => ty -> ty -> ty
sum a b = a <> b

prod : MultiplicativeMonoid ty => ty -> ty -> ty
prod a b = a <> b

interface Ring ty where
  Zero : ty
  One  : ty
  neg : ty -> ty
  inv : ty -> ty
  add : ty -> ty -> ty
  mul : ty -> ty -> ty

infixl 4 -

(-) : Ring ty => ty -> ty -> ty
a - b = a `add` (neg b)


ringCommutator : Ring ty => ty -> ty -> ty
ringCommutator a b = (a `mul` b) `add` (inv (b `mul` a))

ringAntiCommutator : Ring ty => ty -> ty -> ty
ringAntiCommutator a b = (a `mul` b) `add` (b `mul` a)

ringAssociator : Ring ty => ty -> ty -> ty -> ty
ringAssociator x y z = ((x `mul` y) `mul` z) - (x `mul` (y `mul` z))

assocProof : Ring ty => {x : ty} -> ringAssociator x y z = zero
