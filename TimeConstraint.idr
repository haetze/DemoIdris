module TimeContraint 

data In : (a : Type) -> (t : Nat) -> Type where
  InC : (x : a) -> In a t
  
-- data InList : (a : Type) -> (t : Nat) -> Type where
--   Nil : InList a 0
--   (::) : (x : In a t) -> (tail : InList a t') -> InList a (t + t')

-- Constants for Tests
zero : In Nat 0
zero = InC 0

one : In Nat 0
one = InC 1 

transformNat : Nat -> In Nat 1
transformNat n = InC n

-- one_to_four : InList Nat 4
-- one_to_four = transformNat 1 :: transformNat 2 :: transformNat 3 :: transformNat 4 :: Nil



-- simulate costly computation
transformNat' : (n : Nat) -> In Nat n
transformNat' n = InC n

-- Functions
add : In Nat t -> In Nat t' -> In Nat (t+t'+1)
add (InC x) (InC y) = InC (x+y) 

mult : In Nat t -> In Nat t' -> In Nat (t+t'+1)
mult (InC x) (InC y) = InC (x*y) 

-- Proof for multAndAdd
q : (n : Nat) -> 2 + n = 1 + 1 + n
q n = Refl 

q' : {t, t', t'' : Nat} -> 
     (t + t' + t'' = t'' + (t + t')) ->
     (t'' + (t + t') = t'' + t + t') -> t + t' + t'' = t'' + t + t'
q' p_1 p_2 = rewrite p_1 in p_2      

q'' : {t, t', t'' : Nat} -> 
      t'' + ((S Z) + (t + t')) = t'' + (S Z) + (t + t') ->
      (S Z) + (t + t') + t'' = t'' + ((S Z) + (t + t')) ->
      ((S Z) + (t + t') + t'' = t'' + (S Z) + (t + t'))
q'' s t = rewrite t in s


q''' : {t, t', t'' : Nat} -> 
      t'' + ((S Z) + (t + t')) = t'' + (S Z) + (t + t') -> 
      (S Z) + (t + t') + t'' = t'' + (S Z) + (t + t') -> 
      (S Z) + (t + t') + t'' = t'' + ((S Z) + (t + t'))
q''' s t = rewrite s in t

q'''' : {n : Nat} -> ((S Z) + n) + (S Z) = n + (S (S Z))
q'''' {n = Z} = Refl
q'''' {n = (S k)} = cong (q'''' {n = k})

w : {t, t', t'' : Nat} -> 
    ((S Z) + (t + t') + t'') + (S Z) = (t'' + ((S Z) + (t + t'))) + (S Z) ->
    t + t' + t'' + (S (S Z)) =  (t'' + ((S Z) + (t + t'))) + (S Z)
w {t} {t'} {t''} p = rewrite sym (q'''' {n = (t + t') + t''}) in p  

e : {t, t', t'' : Nat} -> 
    t + t' + (S Z) = (S Z) + (t + t') ->
    t + t' + t'' + (S (S Z)) = t'' + ((S Z) + (t + t')) + (S Z) ->
    t + t' + t'' + (S (S Z)) = t'' + (t + t' + (S Z)) + (S Z)
e s t = rewrite s in t  
    
p :  (t : Nat) 
  -> (t' : Nat) 
  -> (t'' : Nat) 
  -> t + t' + t'' + 2 = t + t' + 1 + t'' + 1 
p t t' t'' = let com = plusCommutative (t + t') (S Z) 
                 assoc = plusAssociative (S Z) t t' 
                 r = q' {t = t} {t' = t'} {t'' = S Z} com assoc
                 r' = plusAssociative t'' (S Z) (t + t')
                 r'' = plusCommutative ((S Z) + (t + t')) t''
                 r''' = q'' {t = t} {t' = t'} {t'' = t''} r' r''
                 r'''' = q''' {t = t} {t' = t'} {t'' = t''} r' r'''
                 r''''' = cong {f = (+ (S Z))} r'''' 
                 s = w {t = t} {t' = t'} {t'' = t''} r'''''
                 s' = e {t = t} {t' = t'} {t'' = t''} com s 
                 z = plusCommutative t'' (t + t' + (S Z))
                 in rewrite sym z in s'

-- Example combined function
multAndAdd : In Nat t -> In Nat t' -> In Nat t'' -> In Nat (t+t'+t''+2)
multAndAdd {t} {t'} {t''} x y z = rewrite p t t' t'' in add (mult x y) z

-- Example Calls
test1 : In Nat 5
test1 = multAndAdd (transformNat 10) (transformNat 11) (transformNat 12)


test2 : (n : Nat) -> (m : Nat) -> (l : Nat) -> In Nat (n+m+l+2)
test2 n m l = multAndAdd (transformNat' n) (transformNat' m) (transformNat' l)
