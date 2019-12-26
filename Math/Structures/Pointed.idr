interface Pointed (p : Type -> Type) where
  wrap : a -> p a

interface Copointed (p : Type -> Type) where
  extract : p a -> a


interface LeftUnitalMagma ty where
  id : ty
  op : ty -> ty -> ty

Copointed LeftUnitalMagma where
  extract () = id
