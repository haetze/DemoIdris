module Test 

import Data.Vect


example : Vect 1 Int
example = [1]

data Matrix : (n : Nat) -> (m : Nat) -> (a : Type) -> Type 
  where
    MatrixC : Vect n (Vect m a) -> Matrix n m a


vecPlus : Num a => (u : Vect n a) -> (v : Vect n a) -> Vect n a
vecPlus [] [] = []
vecPlus (x :: xs) (y :: ys) = x + y :: vecPlus xs ys

add : Num t => (a : Vect n (Vect m t)) -> (b : Vect n (Vect m t)) -> Vect n (Vect m t)
add [] [] = []
add (x :: xs) (y :: ys) = vecPlus  x y :: add xs ys

matrixPlus : Num t => (a : Matrix n m t) -> (b : Matrix n m t) -> Matrix n m t
matrixPlus (MatrixC xs) (MatrixC ys) = MatrixC (add xs ys)

row1 : Vect 5 Int 
row1 = [1,2,3,4,5]
row2 : Vect 5 Int 
row2 = [1,2,3,4,5]
row3 : Vect 5 Int 
row3 = [1,2,3,4,5]
row4 : Vect 5 Int 
row4 = [1,2,3,4,5]
row5 : Vect 5 Int 
row5 = [1,2,3,4,5]

m : Matrix 5 5 Int
m = MatrixC [row1,row2,row3,row4,row5]

