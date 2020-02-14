module Language.Parsers

import Builtins
import Math.Functorial.Functor
import Math.Functorial.Applicative

%default total
%access public export

data Parser a = P (String -> [(a, String)])

parse : Parser a -> String -> [(a, String)]
parse (P p) text = p text

RawFunctor Parser where
  map f p =
    P <| \text =>
      case parse p text of
      [] => []
      [(v, out)] => [(f v, out)]

Functor Parser where
  preservesIdentity    = ?rhs_id
  preservesComposition = ?rhs_comp
