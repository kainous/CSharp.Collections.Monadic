module Math.Topological.Pointed

import Builtins

%default total
%access public export

interface Pointed (p : Type -> Type) where
  wrap : a -> p a

-- See where this goes in creating a dictionary...
-- Alone, this demonstrates how to get the type of an object 'via reflection'
PointedObject : Type
PointedObject = (a : Type ** a)

data B = T | F

test0 : PointedObject
test0 = (_ ** T)

test1 : PointedObject
test1 = ((B, B) ** (T, F))

test2 : a -> PointedObject
test2 x = (_ ** x)

test3 : PointedObject
test3 = test2 T

test4 : PointedObject -> Type
test4 (x ** _) = x

test5 : Type
test5 = test4 test3

test6 : (test5 = B)
test6 = ?test6_rhs

--data PointedMorphism (a : PointedObject) (b : PointedObject) where
