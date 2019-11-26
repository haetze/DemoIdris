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

calc_dif : (x : Nat) -> 
           (y : Nat) -> 
           (p : LTQ x y) -> 
           (dif ** dif + x = y)
calc_dif Z y Base = (y ** rewrite plusZeroRightNeutral y in Refl)
calc_dif (S n) (S m) (Ind p) = let (d' ** p') = calc_dif n m p
                                   q = cong {f = S} p'
                               in (d' ** rewrite sym (plusSuccRightSucc d' n) in q)
           


data NotEQNat : Nat -> Nat -> Type where
  BaseZS : NotEQNat Z (S n)
  BaseSZ : NotEQNat (S n) Z
  Step   : NotEQNat n m -> NotEQNat (S n) (S m)

pred : (n : Nat) -> Nat
pred Z = Z
pred (S n) = n

stmt_8 : S k = S l -> k = l
stmt_8 p = cong {f = LTQ.pred} p

||| Proof that
||| \forall n, m. n = m /\ n=/=m => Void
stmt_7 : n = m -> NotEQNat n m -> Void
stmt_7 {n = Z} Refl BaseZS impossible
stmt_7 {n = Z} Refl BaseSZ impossible
stmt_7 {n = Z} Refl (Step _) impossible
stmt_7 {m = Z} Refl BaseZS impossible
stmt_7 {m = Z} Refl BaseSZ impossible
stmt_7 {m = Z} Refl (Step _) impossible
stmt_7 {m = S k} {n = S l} p (Step x) = stmt_7 (stmt_8 p) x 
 
    
data Without : (x : Nat) -> (v : Vect n Nat) -> Type where
  BaseWN : Without x []
  StepWN : (y : Nat) -> NotEQNat x y -> Without x v -> Without x (y :: v)

||| Proof that
||| \forall (xs without x) (ys without x). (xs ++ ys without x)
stmt_6 : Without x xs -> Without x ys -> Without x (xs ++ ys)
stmt_6 BaseWN q = q
stmt_6 (StepWN y z w) q = let rec = stmt_6 w q
                          in StepWN y z rec
    
||| Proof that
||| \forall n,m \in Nat. n =/= m /\ n = m
stmt_5 : Either (NotEQNat n m) (n = m)
stmt_5 {n = Z} {m = Z} = Right Refl
stmt_5 {n = S k} {m = Z} = Left BaseSZ
stmt_5 {n = Z} {m = S l} = Left BaseZS
stmt_5 {n = S k} {m = S l} = case stmt_5 {n = k} {m = l} of
                                  Left p => Left (Step p)
                                  Right p => rewrite p in Right Refl

del' : (x : Nat) -> (v : Vect n Nat) -> (m : Nat ** u : Vect m Nat ** (LTQ m n, Without x u))
del' x [] = (Z ** [] ** (Base, BaseWN))
del' x (y :: xs) = let (k ** u ** (p, q)) = del' x xs
                   in
                      case stmt_5 {n = x} {m = y} of 
                        Left p' => (S k ** y :: u ** (Ind p, StepWN y p' q))
                        Right p' => (k ** u ** (stmt_4 p, q)) 

test : (m ** Vect m Nat)
test = let (m ** v ** (_,_)) = del' 2 test_v in (m ** v)


