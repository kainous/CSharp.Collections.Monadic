import Builtins

data Nat = Z | S Nat

data Bit = I | O

infixr 3 #

data BinNat : Type where
  NN : BinNat
  (#) : Bit -> BinNat -> BinNat

infixl 3 ##
data Sum : Type where
  (##) : Bit -> Bit -> Sum

not : Bit -> Bit
not I = O
not O = I

xor : Bit -> Bit -> Bit
xor I y = not y
xor O y = y

and : Bit -> Bit -> Bit
and I y = y
and O _ = O

-- Higher bit on the right
adb : Bit -> Bit -> Bit -> Pair Bit Bit
adb x y z = ((x `xor` (y `xor` z)), ((x `and` y) `and` z))

fulladd : Bit -> BinNat -> BinNat -> BinNat
fulladd c NN NN = c # NN
fulladd c (x # xs) (y # ys) with (adb c x y)
  | (hi, lo) = lo # fulladd hi xs ys

add : BinNat -> BinNat -> BinNat
add x y = fulladd O x y

mul : BinNat -> BinNat -> BinNat
mul NN _ = NN
mul _ NN = NN
mul (x # xs) (y # ys) = let (x', y') = adb x y O in x' # (y' # (mul xs ys))

parity : BinNat -> Pair Bit BinNat
parity NN = (O, NN)
parity (x # y) = (x, y)

pred : BinNat -> BinNat
pred NN = NN
pred (I # y) = O # y
pred (O # y) = y

iter : BinNat -> (a -> a) -> (a -> a)
iter NN _       = id
iter (O # NN) _ = id
iter (O # xs) f = iter xs (f >> f)
iter (I # xs) f = f >> (iter xs f)

pow : BinNat -> BinNat -> BinNat
pow x y = iter x ((*) y)
