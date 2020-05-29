module Math.Logic.Boolean

import Builtins
--import Prelude.Lazy

%default total
%access public export

data Bool : Type where
  ||| True
  True  : Bool
  False : Bool

interface Boolean a where
  join : a -> a -> a
  meet : a -> a -> a
  implies : a -> a -> a
  complement : a -> a
  bottom : a
  top : a

  meetAssociative : (x, y, z : a) -> x `meet` (y `meet` z) = (x `meet` y) `meet` z
  joinAssociative : (x, y, z : a) -> x `join` (y `join` z) = (x `join` y) `join` z

  meetCommutative : (x, y : a) -> x `meet` y = y `meet` x
  joinCommutative : (x, y : a) -> x `join` y = y `join` x

  meetLeftIdent  : (x : a) -> top `meet` x = x
  meetRightIdent : (x : a) -> x `meet` top = x

  meetLeftAbsorb  : (x : a) -> bottom `meet` x = bottom
  meetRightAbsorb : (x : a) -> x `meet` bottom = bottom

  joinLeftIdent  : (x : a) -> bottom `join` x = x
  joinRightIdent : (x : a) -> x `join` bottom = x

  joinLeftAbsorb  : (x : a) -> top `join` x = top
  joinRightAbsorb : (x : a) -> x `join` top = top

  meetDistributesJoin : (x, y, z : a) -> x `meet` (y `join` z) = (x `meet` y) `join` (x `meet` z)
  joinDistributesMeet : (x, y, z : a) -> x `join` (y `meet` z) = (x `join` y) `meet` (x `join` z)

  deMorgansMeet : (x, y : a) -> complement (x `meet` y) = complement x `join` complement y
  deMorgansJoin : (x, y : a) -> complement (x `join` y) = complement x `meet` complement y

  meetComplementation : (x, y : a) -> x `meet` complement x = bottom
  joinComplementation : (x, y : a) -> x `join` complement y = top

  doubleNegation : (x : a) -> complement (complement x)


and : Bool -> Bool -> Bool
and True  x = x
and False _ = False

||| Two implementations for And and Or
--and' : Bool -> Lazy Bool -> Bool
--and' True  x = Force x
--and' False _ = False

or : Bool -> Bool -> Bool
or True _ = True
or False x = x

--or' : Bool -> Lazy Bool -> Bool
--or' True _  = True
--or' False x = Force x

not : Bool -> Bool
not True  = False
not False = True

notnotIs : .(a : Bool) -> a = not (not a)
notnotIs True  = Refl
notnotIs False = Refl

Uninhabited (True = False) where
  uninhabited Refl impossible

Uninhabited (False = True) where
  uninhabited Refl impossible
