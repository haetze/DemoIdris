module Fin

import Data.Vect
import Sort

data F : (n : Nat) -> Type where
  F_Z : F n 
  F_S : F n -> F (S n)
  
  
  
example : F 10
example = F_S F_Z


idx : Vect (S n) a -> F n -> a
idx (x :: xs) F_Z = x
idx (x :: xs) (F_S y) = idx xs y 



exV : Vect 17 Int
exV = [1,2,3,4,5,6,7,8,9,1,2,3,4,5,76,78,9]

data LTQ : (a : Nat) -> (b : Nat) -> Type where
  Zero : (b : Nat) -> LTQ Z b 
  Step : LTQ a b -> LTQ (S a) (S b)



||| Proof that 10 <= 16
p : LTQ 10 16
p = Step (Step (Step (Step (Step (Step (Step (Step (Step (Step (Zero 6)))))))))) 

s : F n -> LTQ n m -> F m
s F_Z (Zero m) = F_Z 
s F_Z (Step x) = F_Z 
s (F_S x) (Step y) = F_S (s x y)

idx' : (v : Vect (S m) a) -> (n : F k) -> (p : LTQ k m) -> a
idx' v n p = idx v (s n p)
