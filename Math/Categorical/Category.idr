module Math.Categorical.Category

import Builtins
import Math.Categorical.Semigroupoid
import Math.Order.Preorder

%default total
%access public export

namespace Categorical
  -- The difference between PreorderedSet and Category is the demand for neutrality over the composition
  -- Otherwise, there is no difference between a Semigroupoid and a Math.Order.Transitive
  -- The problem is in that "Transitive" is a word for relations and "Compose" is a word for "functions"
  -- There is not a common word.
  -- More confusingly, there is a meaning for "composing" relations which is closer to the meaning ascribed
  -- by "function composition".

  interface (RawSemigroupoid mor) => RawCategory (mor : obj -> obj -> Type) where
    id : mor a a

  --RawCategory mor => PreorderedSet mor where
    --refl = id
    --trans = compose

  interface (RawCategory mor, Semigroupoid mor) => Category (mor : obj -> obj -> Type) where
    idIsLeftUnital  : {x : mor a b} -> id >> x = x
    idIsRightUnital : {x : mor a b} -> x >> id = x

  --RawSemigroupoid mor => Reflexive mor where
    --refl = id



  --RawCategory mor => PreorderedSet (mor : obj -> obj -> Type)
    --trans = compose
