module Zip 

import Data.Vect

zipZ : Vect n a -> Vect n b -> Vect n (a, b)
zipZ [] v_b = []
zipZ (x :: xs) (y :: ys) = (x, y) :: zipZ xs ys

zipZ3 : Vect n a -> Vect n b -> Vect n c -> Vect n (a,b,c)
zipZ3 [] ys zs = []
zipZ3 (x :: xs) (y :: ys) (z :: zs) = (x, y, z) :: zipZ3 xs ys zs

