module LTQ 

import Data.Vect

data LTQ : (a : Nat) -> (b : Nat) -> Type where
  Base : LTQ Z n
  Ind : (p : LTQ n m) -> LTQ (S n) (S m)
  

||| Proof that 
||| \forall n,m\in N. (n + 1 <= m) => 
|||                    (\exists x\in N. x+1 = m)
total
stmt_1 : LTQ (S n) m -> (x:Nat  ** m = S x)
stmt_1 {m = S x} p = (x ** Refl)

||| Proof that
||| \forall n,m in N. n <= m /\ m <= n
total
stmt_2 : Either (LTQ n m) (LTQ m n)
stmt_2 {n = Z} = Left Base
stmt_2 {m = Z} = Right Base
stmt_2 {n = S k} {m = S l} = case stmt_2 {n = k} {m = l} of 
                                  Left p  => Left (Ind p)
                                  Right p => Right (Ind p)

||| Proof that
||| \forall n, m in N. S n <= m => n <= m
total
stmt_3 : (p : LTQ (S n) m) -> LTQ n m
stmt_3 {n = Z} _ = Base 
stmt_3 {n = S k} (Ind p) = Ind (stmt_3 p)

||| proof that
||| \forall n, m \in N. n <= m => n <= S m
total
stmt_4 : (p : LTQ n m) -> LTQ n (S m)
stmt_4 {n = Z} p = Base
stmt_4 {n = S k} (Ind p) = Ind (stmt_4 p)

del : Eq a => (x : a) -> (v : Vect n a) -> (m ** (Vect m a, LTQ m n))
del x [] = (0 ** ([], Base))
del x (y :: xs) = let 
                      (k ** (v, p)) = del x xs 
                  in if x == y then (k ** (v, stmt_4 p)) 
                               else (S k ** (y :: v, Ind p))

test_v : Vect 5 Nat
test_v = [1,2,3,4,5]
