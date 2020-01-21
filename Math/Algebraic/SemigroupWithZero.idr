import Builtins
import Prelude.Lazy

infixl 4 <>, &&

data Bool = True | False

interface SemigroupWithZero ty where
  (<>) : ty -> Lazy ty -> ty

(&&) : Bool -> Lazy Bool -> Bool
True  && x = force x
False && _ = False
