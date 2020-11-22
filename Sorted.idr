module Sorted
sorted' : Ord a => List a -> Bool
sorted' [] = True
sorted' (x :: []) = True
sorted' (x :: (y :: xs)) = x <= y && sorted' (y :: xs) 

data ABC : Type -> Type -> Type -> Type where
  A : (x : a) -> ABC a b c
  B : (x : b) -> ABC a b c
  C : (x : c) -> ABC a b c

s : (a : Bool) -> (b : Bool) -> (a && b = True) -> (a = True, b = True)
s False False Refl impossible
s False True Refl impossible
s True False Refl impossible
s True True prf = (Refl, Refl)

r : Ord a => (l : List a)
          -> (x : a)
          -> (y : a)
          -> Sorted.sorted' (x :: y :: l) = True 
          -> ((x <= y) = True, Sorted.sorted' (y :: l) = True)
r l x y prf = s (x <= y) (sorted' (y::l)) prf


p : Ord a => (l : List a) 
          -> Sorted.sorted' l = True 
          -> ABC (l = []) (x : a ** l = [x]) (x : a ** y : a ** l' : List a ** (l = x :: y :: l', Sorted.sorted' (y :: l') = True, x <= y = True))
p [] prf = A Refl
p (x :: []) prf = B (x ** Refl)
p (x :: (y :: xs)) prf = let (prf_1, prf_2) = r xs x y prf in C (x ** y ** xs ** (Refl, prf_2, prf_1))

order : Ord a => (x : a)
              -> (y : a)
              -> (b : Bool ** x <= y = b)
order x y = (x <= y ** Refl)

-- This would need to be a requirement for the Ord class.....
order' : Ord a => (x : a)
               -> (y : a)
               -> x <= y = False
               -> y <= x = True
order' x y prf = ?h               

sorted_from_facts : Ord a => (l : List a)
                          -> (y : a)
                          -> (Sorted.sorted' (y :: l) = True)
                          -> (x : a)
                          -> (x <= y = True)
                          -> (Sorted.sorted' (x :: y :: l) = True)
sorted_from_facts l y prf x prf' = rewrite prf in 
                                   rewrite prf' in Refl
                                   
total
lem : (a : t)
    ->(as : List t)
    ->(b : t)
    ->(b': t)
    ->(bs : List t)
    -> a :: as = b :: b' :: bs 
    -> a = b 
lem _ [] _ _ _ Refl impossible
lem b (b' :: bs) b b' bs Refl = Refl

insert : Ord a => (l : List a)
               -> {auto non_empty : NonEmpty l}
               -> Sorted.sorted' l = True
               -> (x : a)
               -> (e : a ** l' : List a ** (Sorted.sorted' (e::l') = True, Either (e = x) (e = head l)))
insert (y :: xs) prf x = let (b ** prf') = order x y
                         in case b of
                            True => (x ** (y :: xs) ** (sorted_from_facts xs y prf x prf', Left Refl))
                            False => let prf_1' = order' x y prf'
                                     in case p (y :: xs) prf of
                                        B (y' ** prf_1) => (y ** x :: [] ** (sorted_from_facts [] x Refl y prf_1', Right Refl))
                                        C (y' ** y'' ** l' ** (p1,p2,p3)) => let (h ** l'' ** (prf_1, either)) = insert (y''::l') p2 x 
                                                                             in case either of
                                                                                Left w => (y ** h::l'' ** (rewrite prf_1 in rewrite w in rewrite prf_1' in Refl, Right Refl))
                                                                                Right w => (y ** h :: l'' ** (rewrite prf_1 in rewrite w in rewrite lem y xs y' y'' l' p1 in rewrite p3 in Refl, Right Refl))



ex : List Integer
ex = [1,2,3,4,5,6]


ex_sorted : (Sorted.sorted' [1,2,3,4,5] = True)
ex_sorted = Refl
 
