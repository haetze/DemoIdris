module Fin

import Data.Vect

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



