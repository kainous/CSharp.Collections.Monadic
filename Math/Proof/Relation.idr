-- We consider a relation to be a type of (a -> b -> Type)

using (A, B : Type)
  Relation : A -> B -> Type
  Relation x y = ?Relation_rhs

--Endorelation : obj -> Relation obj obj
--Endorelation obj = Endorelation obj

data Nat = Z | S Nat

--test0 : Relation Nat Nat
--test0 = (=)
