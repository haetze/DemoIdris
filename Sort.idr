module Sort

import Data.Vect

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


