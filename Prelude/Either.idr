module Prelude.Either

import Builtins
--import Math.Functorial.Bifunctor

%default total
%access public export

data Either a b
  = Left a
  | Right b
