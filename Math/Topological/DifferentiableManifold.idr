import Builtins

infixl 4 +, -, *, /
infixl 4 <+>, *>

interface Ring ty where
  zero : ty
  one  : ty
  (+)  : ty -> ty -> ty
  (-)  : ty -> ty -> ty
  (*)  : ty -> ty -> ty
  inv  : ty -> ty
  neg  : ty -> ty
  fromInteger : Integer -> ty

--- Additive would be useful here

interface Ring s => Vector s v where
  zeroV : v
  (<+>)  : v -> v -> v
  (*>)  : s -> v -> v
  negV : v -> v
  associativeAddition : x <+> (y <+> z) = (x <+> y) <+> z
  commutativeAddition : x <+> y = y <+> x
  leftAdditiveIdentity : x = zeroV <+> x
  rightAdditiveIdentity : x = x <+> zeroV
  leftMultiplicativeIdentity : x = one *> x
  negIsInverse : x <+> negV x = zeroV
  multiplicationCompatibility : a *> (b *> x) = (a * b) *> x
  vectorDistribution : a *> (x <+> y) = (a *> x) <+> (a *> y)
  scalarDistribution : (a + b) *> x = (a *> x) <+> (b *> x)

congFunct : (d : (ty -> ty) -> (ty -> ty)) -> (f = g) -> (d f = d g)
congFunct _ Refl = Refl

data Endomorphism ty = Endo (ty -> ty)

-- How to specify that this moves from an Affine Space to a Vector Space??
interface Ring ty => DifferentiableManifold ty where
  D : (ty -> ty) -> (ty -> ty)

  additivity  : (f, g : ty -> ty) -> D (\y => f y + g y) x = D f x + D g x
  productRule : (f, g : ty -> ty) -> D (\y => f y * g y) x = D f x * g x + f x * D g x
  chainRule   : (f, g : ty -> ty) -> D (f >> g) x = (D f >> g) x * D g x

  --avsasdf : (f, g : ty -> ty) -> D (\y => (f y) * (f y) + (g y) * (g y))

Ring ty => Ring (Endomorphism ty) where
  (Endo f) + (Endo g) = Endo (\x => f x + g x)
  (Endo f) * (Endo g) = Endo (\x => f x * g x)
  inv (Endo f) = Endo (\x => inv (f x))
  neg (Endo f) = Endo (\x => neg (f x))
  fromInteger n = Endo (\x => fromInteger n)
  zero = fromInteger 0
  one = fromInteger 1


-- interface (Ring ty, Vector ty) => Algebra ty


--asdofin : DifferentiableManifold ty => (f, g : ty -> ty) -> D (\y => (f y + g y) * (f y + g y)) x = D (\y => (f y) * (f y) + 2 * (f y) * (g y) + (g y) * (g y)) x
--asdofin f g = congFunct D (\y => (f y + g y) * (f y + g y) = (f y) * (f y) + 2 * (f y) * (g y) + (g y) * (g y))

  -- prove chain rule in terms of product rule

  -- ((f+g)^2)' = 2(f+g)(f+g)' = 2ff'+2fg'+2gf'+2gg'
  -- (f^2 +2fg + g^2)' = 2ff' + 2(fg)' + 2gg'
  -- 2(fg)' = 2fg' + 2f'g
