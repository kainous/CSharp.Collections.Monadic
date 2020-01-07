module Math.Logic.Boolean

import Builtins
import Prelude.Lazy

%default total
%access public export

data Bool : Type where
  ||| True
  True  : Bool
  False : Bool


and : Bool -> Bool -> Bool
and True  x = x
and False _ = False

||| Two implementations for And and Or
and' : Bool -> Lazy Bool -> Bool
and' True  x = Force x
and' False _ = False

or : Bool -> Bool -> Bool
or True _ = True
or False x = x

or' : Bool -> Lazy Bool -> Bool
or' True _  = True
or' False x = Force x

not : Bool -> Bool
not True = False
not False = True

Uninhabited (True = False) where
  uninhabited Refl impossible

Uninhabited (False = True) where
  uninhabited Refl impossible
