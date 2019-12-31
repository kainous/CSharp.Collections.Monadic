module Math.Categorical.Category

import Builtins
import Math.Categorical.Semigroupoid

%default total
%access public export

interface Semigroupoid' mor => Category' (mor : obj -> obj -> Type) where
  cid : mor a a

interface (Category' mor, Semigroupoid mor) => Category (mor : obj -> obj -> Type) where
  idIsLeftUnital  : {x : mor a b} -> cid << x = x
  idIsRightUnital : {x : mor a b} -> x << cid = x
