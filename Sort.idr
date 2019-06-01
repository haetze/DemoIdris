module Sort

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

data ContainAllElems : (v : Vect n a) -> (u : Vect m a) -> Type where
  Introduce : (u : Vect n a) -> ContainAllElems [] u
  Add : (x : a) -> ContainAllElems v u -> Contains x u -> ContainAllElems (x :: v) u

stmt' : (v : Vect n Nat) -> (u : Vect (S m) Nat) -> Either (ContainAllElems v u) ()
stmt' [] ys = Left (Introduce ys)
stmt' (x :: xs) u = let r = statement_1 x u 
                        s = stmt' xs u in
                    case r of 
                    Left p => case s of 
                              Right () => Right ()
                              Left q => Left (Add x q p)
                    Right () => Right ()



stmt : (v : Vect n Nat) -> (u : Vect n Nat) -> Either (ContainAllElems v u
                                                      ,ContainAllElems u v) ()
stmt [] [] = Left (Introduce [], Introduce [])
stmt (h::t) (h'::t') = let r = stmt' (h::t) (h'::t') 
                           s = stmt' (h'::t') (h::t)  in 
                       case r of 
                       Right _ => Right ()
                       Left p  => case s of 
                                  Right _ => Right ()
                                  Left q  => Left (p, q)



statement' : (v : Vect n Nat) -> (u : Vect n Nat) -> Bool
statement' [] [] = True
statement' (x :: xs) u = case statement_1 x u of 
                          Left p => statement' xs (rem x u p)
                          Right () => False 
                        
                                     
 
 


data LTQ : (a : Nat) -> (b : Nat) -> Type where
  Zero : (b : Nat) -> LTQ Z b 
  Step : LTQ a b -> LTQ (S a) (S b)


lessthanproof_1_lt_2 : LTQ 1 2
lessthanproof_1_lt_2 = Step (Zero 1)

lessthanproof_3_lt_5 : LTQ 3 5
lessthanproof_3_lt_5 = Step (Step (Step (Zero 2)))

||| Proof that for all 2 natural number a and b 
||| either a <= b or b <= a.
statement : (a : Nat) -> (b : Nat) -> Either (LTQ a b) (LTQ b a)
statement Z b = Left (Zero b)
statement a Z = Right (Zero a) 
statement (S k) (S j) = case statement k j of 
                             Left p => Left (Step p)
                             Right p => Right (Step p)

data SVect : (n : Nat) -> (head : Nat) -> Type where
  N    : (x : Nat) -> SVect (S Z) x
  Cons : (x : Nat) -> SVect n h -> LTQ x h -> SVect (S n) x 

toVect : (v : SVect n h) -> Vect n Nat
toVect (N h) = [h]
toVect (Cons h x y) = h :: toVect x                                          


combineEmpty : (x : Nat) -> (v : Vect Z Nat) -> SVect (S Z) x
combineEmpty x [] = N x

insert : (x : Nat) -> (v : SVect n h) -> Either (SVect (S n) x) (SVect (S n) h)
insert x (N h) = case statement x h of
                      Left p => Left (Cons x (N h) p)
                      Right p => Right (Cons h (N x) p)
insert x l@(Cons h y p) = case statement x h of 
                             Left q => (Left (Cons x l q))
                             Right q => case insert x y of
                                             Left l => Right (Cons h l q)
                                             Right l => Right (Cons h l p)

total
sort : (v : Vect n Nat) -> SVect (S n) Z
sort [] = N Z
sort (x :: xs) = case sort xs of 
                   (N Z)        => Cons Z (N x) (Zero x)
                   (Cons Z t p) => case insert x t of
                                     Left l@(Cons h' t' q) => Cons Z l (Zero h') 
                                     Right l@(Cons h' t' q) => Cons Z l (Zero h') 

p : (v : Vect n Nat) -> ContainAllElems (toVect (sort v)) (Z::v)
p [] = Add 0 (Introduce [0]) (B 0 [])
p (y :: ys) = let r = p ys in ?h
              

 
 
