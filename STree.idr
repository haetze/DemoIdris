module STree 


data STE : Nat -> Nat -> Type where
  E2Z : (x : Nat) -> STE Z x
  Stp : STE x y -> STE (S x) (S y)
  
  
  
fiveSmallerNine : STE 5 9
fiveSmallerNine = Stp (Stp (Stp (Stp (Stp (E2Z 4)))))

order : (x : Nat) -> (y : Nat) -> Either (STE x y) (STE y x)
order Z y = Left (E2Z y)
order (S k) Z = Right (E2Z (S k))
order (S k) (S j) = case (order k j) of
                    Left p => Left (Stp p)
                    Right p => Right (Stp p)

trans : STE x y -> STE y z -> STE x z
trans {z} (E2Z y) q = E2Z z
trans (Stp z) (Stp x) = Stp (trans z x)

refl : (a : Nat) -> STE a a
refl Z = E2Z 0
refl (S k) = Stp (refl k)

mmin : Nat -> Nat -> Nat
mmin Z b = Z
mmin (S k) Z = Z
mmin (S k) (S j) = S (mmin k j)

mmax : Nat -> Nat -> Nat
mmax Z y = y
mmax (S k) Z = S k
mmax (S k) (S j) = S (mmax k j)

mmin_trans : (a : Nat) -> (b : Nat) -> (c : Nat) -> S a = mmin (S b) (S c) -> a = mmin b c
mmin_trans Z Z c p = Refl
mmin_trans Z (S k) Z p = Refl
mmin_trans Z (S _) (S _) Refl impossible
mmin_trans (S _) Z Z Refl impossible
mmin_trans (S _) Z (S _) Refl impossible
mmin_trans (S _) (S _) Z Refl impossible
mmin_trans (S (mmin j i)) (S j) (S i) Refl = Refl

mmax_trans : (a : Nat) -> (b : Nat) -> (c : Nat) -> S a = mmax (S b) (S c) -> a = mmax b c
mmax_trans Z Z Z p = Refl
mmax_trans Z Z (S _) Refl impossible
mmax_trans Z (S _) Z Refl impossible
mmax_trans Z (S _) (S _) Refl impossible
mmax_trans (S _) Z Z Refl impossible
mmax_trans (S j) Z (S j) Refl = Refl
mmax_trans (S j) (S j) Z Refl = Refl
mmax_trans (S (mmax j i)) (S j) (S i) Refl = Refl

fromMin1 : (x : Nat) -> (y : Nat) -> x = mmin x y -> STE x y
fromMin1 Z y p = E2Z y
fromMin1 (S _) Z Refl impossible
fromMin1 (S k) (S j) p = Stp (fromMin1 k j (mmin_trans k k j p))

fromMin2 : (x : Nat) -> (y : Nat) -> y = mmin x y -> STE y x
fromMin2 Z Z Refl = E2Z 0
fromMin2 Z (S _) Refl impossible
fromMin2 (S k) Z p = E2Z (S k)
fromMin2 (S k) (S j) p = Stp (fromMin2 k j (mmin_trans j k j p))

                              
fromMax1 : (x : Nat) -> (y : Nat) -> x = mmax x y -> STE y x
fromMax1 Z Z Refl = E2Z 0
fromMax1 Z (S _) Refl impossible
fromMax1 (S k) Z p = E2Z (S k)
fromMax1 (S k) (S j) p = Stp (fromMax1 k j (mmax_trans k k j p))

fromMax2 : (x : Nat) -> (y : Nat) -> y = mmax x y -> STE x y
fromMax2 Z y p = E2Z y
fromMax2 (S _) Z Refl impossible
fromMax2 (S k) (S j) p = Stp (fromMax2 k j (mmax_trans j k j p))                 
                                                
