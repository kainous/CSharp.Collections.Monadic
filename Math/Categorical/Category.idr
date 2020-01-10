module Math.Categorical.Category

import Builtins
import Math.Categorical.Semigroupoid
import Math.Order.Preorder

%default total
%access public export

namespace Categorical
  interface RawSemigroupoid mor => RawCategory (mor : obj -> obj -> Type) where
    id : mor a a

  interface (RawCategory mor, Semigroupoid mor) => Category (mor : obj -> obj -> Type) where
    idIsLeftUnital  : {x : mor a b} -> id >> x = x
    idIsRightUnital : {x : mor a b} -> x >> id = x

  --RawSemigroupoid mor => Reflexive mor where
    --refl = id



  --RawCategory mor => PreorderedSet (mor : obj -> obj -> Type)
    --trans = compose
