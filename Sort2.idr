module Sort2

import Data.Vect

p : (a : Nat) 
 -> (b : Nat)
 -> S a + b = a + S b
p Z b = Refl
p (S k) b = let r = p k b in cong r 

p' : S a + b = S l -> a + S b = S l
p' {a} {b} {l} w = let q = p a b in rewrite sym q in w

q : (a : Nat)
 -> (b : Nat)
 -> a + (S Z + b) = S (a + b)
q a b = let q' = plusCommutative a (S b)
            q'' = plusCommutative b a
        in rewrite sym q'' in q'

merge : Ord a => Vect n a -> Vect m a -> Vect (m+n) a
merge {n = Z} {m} [] ys = rewrite (plusZeroRightNeutral m) in ys
merge {n} {m = Z} xs [] = xs
merge {n = S k} {m = S l} (x :: xs) (y :: ys) = if x < y 
                                                then 
                                                  let v = Sort2.merge xs (y::ys)
                                                      r = p l k
                                                  in rewrite sym r in x::v
                                                else 
                                                  let v = Sort2.merge (x::xs) ys
                                                  in y :: v
                                                  
                                                  
split : Ord a => Vect n a -> a -> (m ** 
                                   m' ** 
                                   v : Vect m a ** 
                                   v' : Vect m' a ** 
                                   m + m' = n)
split [] a = (Z ** Z ** [] ** [] ** Refl)
split (x :: xs) a = let (m ** m' ** v ** v' ** p) = split xs a
                    in if x < a
                       then 
                         let m_ = S m
                             v_ = x :: v
                         in (m_ ** m' ** v_ ** v' ** cong p) 
                       else 
                         let m_ = S m'
                             v_ = x :: v'
                             r = cong {f = S} p
                             r' = p' {a = m} {b = m'} r
                         in (m ** m_ ** v ** v_ ** r')
                         
rew : m + m' = len 
   -> m + (S Z + m') = S (m + m')
   -> m + (S Z + m') = S len
rew p q = rewrite sym p in q   

sort : Ord a => Vect n a -> Vect n a
sort [] = []
sort (x::xs) = let (m ** m' ** v ** v' ** p) = Sort2.split xs x
                   vs = Sort2.sort (assert_smaller (x::xs) v)
                   vs'= Sort2.sort (assert_smaller (x::xs) v')
                   res= vs ++ [x] ++ vs'
                   prf= q m m'
                   pr' = rew {m} {m'} p prf
               in rewrite sym pr' in res
 


 
