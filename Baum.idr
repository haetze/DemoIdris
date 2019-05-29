module Baum 

import Data.Vect

pSRSucc : (l : Nat) -> (r : Nat) -> S (plus l r) = plus l (S r)
pSRSucc Z r = Refl
pSRSucc (S k) r = let ih = pSRSucc k r in cong ih

pSLSucc : (l : Nat) -> (r : Nat) -> S (plus l r) = plus (S l) r
pSLSucc _ _ = Refl


plus_com : (n : Nat) -> (m : Nat) -> plus n m = plus m n 
plus_com Z Z = Refl
plus_com Z (S l) = cong (plus_com Z l)
plus_com (S k) m = let r = plus_com k m in
                       rewrite r in 
                         rewrite pSRSucc m k in Refl

plus_1 : (n : Nat) -> (m : Nat) -> S (S (plus n m)) = plus (S n) (S m)
plus_1 n m = let i = pSRSucc n m
                 j = pSLSucc n (S m) in rewrite i in j
plus_3 : (n : Nat) -> plus n (S Z) = S n
plus_3 Z = Refl
plus_3 (S k) = cong (plus_3 k)

plus_4 : (n: Nat) -> (m:Nat) -> S (plus n m) = plus n (plus m (S Z))
plus_4 n m = let r = pSRSucc n m 
                 s = plus_3 m in rewrite s in r 

plus_2 : (n:Nat) -> (m:Nat) -> (n + (m + 1)) = S (plus n m)
plus_2 n m = let k = plus_4 n m in sym k 

data Tree : (a : Type) -> (s : Nat) -> Type where
  Empty : Tree a 0
  Fork  : (l : Tree a n) -> (x : a) -> (r : Tree a m) -> Tree a (S (n+m))

inorder : (t : Tree a n) -> Vect n a
inorder Empty = []
inorder (Fork l x r) = let l' = inorder l
                           r' = inorder r 
                           result = l' ++ [x] ++ r' in 
                           prf result
  where
    prf : Vect (n + ((S Z) + m)) a -> Vect (S (plus n m)) a
    prf {n} {m} t = rewrite pSRSucc n m in t


preorder : (t : Tree a n) -> Vect n a
preorder Empty = []
preorder (Fork l x r) = let l' = preorder l 
                            r' = preorder r 
                            result = x :: l' ++ r' in
                            result
                            
                            
prf2 : Vect (plus n (plus m (S Z))) a -> Vect (S (plus n m)) a
prf2 {n} {m} t = rewrite plus_4 n m in t



postorder : (t : Tree a n) -> Vect n a 
postorder Empty = []
postorder (Fork l x r) = let l' = postorder l
                             r' = postorder r
                             result = l' ++ (r' ++ [x]) in 
                             prf2 result



test : Tree Int 3
test = Fork (Fork Empty 1 Empty) 2 (Fork Empty 3 Empty)
                      

    

 
 
 
 
