module VecEq.idr

import Data.Vect

||| Proof that x is in v. 
data Contains : (x : a) -> (v : Vect (S n) a) -> Type where
  B : (x : a) -> (v : Vect n a) -> Contains x (x :: v)
  C : (x : a) -> (y : a) -> Contains x v ->  Contains x (y :: v)

single : (x : a) -> Contains x [x]
single x = B x [] 

eqAdd : (x : a) -> (y : a) -> y = x -> (v : Vect n a) -> Contains x (y :: v)
eqAdd x y p v = rewrite p in B x v 

eqSt : (x : Nat) -> (y : Nat) -> Either (x = y) ()
eqSt Z Z = Left Refl
eqSt Z (S k) = Right ()
eqSt (S k) Z = Right ()
eqSt (S k) (S j) = case eqSt k j of
                     Right () => Right ()
                     Left p => Left (cong p)

||| Removes one x from v or the last element of 
||| the Vect.
rem : Eq a => (x : a) -> (v : Vect (S n) a) -> Contains x v -> Vect n a
rem x (x :: xs) (B x xs) = xs
rem x (y :: xs) (C x y z) = y :: rem x xs z


||| Proof that x is either in v or not
statement_1 : (x : Nat) -> (v : Vect (S n) Nat) -> Either (Contains x v) ()
statement_1 x (y :: []) = case eqSt x y of 
                            Left p => Left (eqAdd x y (sym p) [])
                            Right () => Right ()
statement_1 x (y :: ys@(y' :: ys')) = case eqSt x y of 
                            Left p => Left (eqAdd x y (sym p) (y' :: ys'))
                            Right () => let r = statement_1 x (y' :: ys')
                                        in case r of 
                                             Left p => Left (C x y p)
                                             Right () => Right ()
                                             
statement : (v : Vect n Nat) -> (u : Vect n Nat) -> Bool
statement [] [] = True
statement (x :: xs) u = case statement_1 x u of 
                          Left p => statement xs (rem x u p)
                          Right () => False 
                        
                                     
 
 
