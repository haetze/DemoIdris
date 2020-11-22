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
