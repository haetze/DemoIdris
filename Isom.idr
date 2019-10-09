module Isom



-- swap : (a, b) -> (b, a)
-- swap (a,b) = (b, a)

||| Proof that
||| A x B \cong B x A
swapRec : (a, b) = swap (swap (a, b))
swapRec = Refl


||| Datatype for N_{>0}
data SN : Type where
  I : SN
  A : SN -> SN
  
sn_to_n : SN -> Nat
sn_to_n I = Z
sn_to_n (A x) = S (sn_to_n x)

n_to_sn : Nat -> SN
n_to_sn Z = I
n_to_sn (S k) = A (n_to_sn k)


||| Proof(1) that
||| N_{>0} \cong N
sn_cong_n_1 : n = sn_to_n (n_to_sn n)
sn_cong_n_1 {n = Z} = Refl
sn_cong_n_1 {n = (S k)} = let r = sn_cong_n_1 {n = k} in cong r

||| Proof(2) that
||| N_{>0} \cong N
sn_cong_n_2 : n = n_to_sn (sn_to_n n)
sn_cong_n_2 {n = I} = Refl
sn_cong_n_2 {n = (A x)} = let r = sn_cong_n_2 {n = x} in cong r
