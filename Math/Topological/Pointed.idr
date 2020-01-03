module Math.Topological.Pointed

import Builtins

%default total
%access public export

interface Pointed (p : Type -> Type) where
  wrap : a -> p a