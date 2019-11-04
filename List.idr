module List 

import Data.Vect

b_to_prop : Bool -> Type
b_to_prop False = Void
b_to_prop True = ()

lt : Nat -> Nat -> Bool
lt Z Z = False
lt Z (S k) = True
lt (S k) Z = False
lt (S k) (S j) = List.lt k j


index_ : (v : Vect n a) -> (i : Nat) -> b_to_prop (List.lt i n) -> a
index_ [] Z p impossible
index_ [] (S k) p impossible
index_ (x :: xs) Z p = x
index_ (x :: xs) (S k) p = index_ xs k p

call : Nat
call = index_ [1,2,3,4] (S (S Z)) () 
