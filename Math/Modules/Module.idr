module Math.Modules.Module

infixl 4 #>, <#, +, *, <#>



interface AdditiveGroup ty where
  (+) : ty -> ty -> ty
  inv : ty -> ty
  unit : ty

  commutative : a + b = b + a
  associative : a + (b + c) = (a + b) + c
  identity : a + unit = a
  inverse : a + inv a = unit

interface AdditiveGroup ty => Ring ty where
  (*) : ty -> ty -> ty
  associativeMult : a * (b * c) = (a * b) * c

interface Ring ty => Field ty where

interface (Ring scalar, AdditiveGroup vector) => LeftModule scalar vector where
  (#>) : scalar -> vector -> vector
  scalarDistributivity : r #> (x + y) = (r #> x) + (r #> y)
  vectorDistributivity : (r + s) #> x = (r #> x) + (s #> y)
  compatibility : (r * s) #> x = r #> (s #> x)

interface (Ring scalar, AdditiveGroup vector) => RightModule scalar vector where
  (<#) : vector -> scalar -> vector

interface (LeftModule scalar vector, RightModule scalar vector) => Bimodule scalar vector where

interface (Field scalar, Bimodule scalar vector) => Vector scalar vector where
