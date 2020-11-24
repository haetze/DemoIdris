module View


data Pred : Nat -> Type where
  P : (n : Nat) -> {auto p : S (S m) = n} -> Pred (m + 2)



prf : (S m) = (S n) -> m = n
prf {m = Z} {n = Z} p = Refl
prf {m = Z} {n = (S _)} Refl impossible
prf {m = (S _)} {n = Z} Refl impossible
prf {m = (S k)} {n = (S k)} Refl = Refl 

prf_2 : (k : Nat) -> k + 2 = S (S k)
prf_2 Z = Refl
prf_2 (S k) = let p = prf_2 k in cong p

pred : (x : Nat) -> {auto p : S (S m) = x} -> Pred x
pred Z {p = Refl} impossible
pred (S Z) {p = Refl} impossible
pred (S (S k)) {p = p} = let r = prf_2 k
                         in rewrite sym r in P (S (S k)) 


f : (x : Nat) -> {auto p : S (S m) = x} -> Nat
f x with (View.pred x)
    f  (m + S (S Z)) | (P n) = m
    
    
    
data Split : Nat -> Type where
  Sp : (n : Nat) -> (m : Nat) -> Split (n + m)

prf_3 : (n : Nat) -> (m : Nat) -> S (S (n + m)) = (S n) + (S m)
prf_3 Z m = Refl
prf_3 (S k) m = let p = prf_3 k m in cong p

  
split : (n : Nat) -> Split n
split Z = Sp Z Z
split (S Z) = Sp (S Z) Z
split (S (S k)) = let Sp n m = split k in rewrite prf_3 n m in Sp (S n) (S m)


g : (x : Nat) -> (Nat, Nat)
g x with (split x)
  g (n + m) | (Sp n m) = (n,m)
