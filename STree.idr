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

total 
minFromP : (a : Nat) -> (b : Nat) -> STE a b -> a = (mmin a b)
minFromP Z b p = Refl
minFromP (S _) Z (E2Z _) impossible
minFromP (S _) Z (Stp _) impossible
minFromP (S k) (S j) (Stp x) = cong {f = S} (minFromP k j x)

minFromP' : STE a b -> a = (mmin a b)
minFromP' {a} {b} p = minFromP a b p

total
maxFromP : (a : Nat) -> (b : Nat) -> STE a b -> b = (mmax a b)
maxFromP Z b p = Refl
maxFromP (S _) Z (E2Z _) impossible
maxFromP (S _) Z (Stp _) impossible
maxFromP (S k) (S j) (Stp x) = cong {f = S} (maxFromP k j x)

maxFromP' : STE a b -> b = (mmax a b)
maxFromP' {a} {b} p = maxFromP a b p
                                                                                                        
total
minKom : (a : Nat) -> (b : Nat) -> mmin a b = mmin b a
minKom Z Z = Refl
minKom Z (S k) = Refl
minKom (S k) Z = Refl
minKom (S k) (S j) = cong (minKom k j)

total 
maxKom : (a : Nat) -> (b : Nat) -> mmax a b = mmax b a
maxKom Z Z = Refl
maxKom Z (S k) = Refl
maxKom (S k) Z = Refl
maxKom (S k) (S j) = cong (maxKom k j)

data STree : Nat -> Nat -> Type where
  Empt : STree a a
  Fork : STree a b -> 
         STree c d -> 
         (e : Nat) -> 
         STE b e -> 
         STE e c ->
         STE a b ->
         STE c d -> STree a d

two_to_min : STE a b -> STE a c -> STE a (mmin b c)
two_to_min {a = Z} {b = b} {c = c} p q = E2Z (mmin b c)
two_to_min {a = (S _)} {b = Z} {c = Z} (E2Z _) _ impossible
two_to_min {a = (S _)} {b = Z} {c = Z} (Stp _) _ impossible
two_to_min {a = (S _)} {b = Z} {c = (S _)} (E2Z _) _ impossible
two_to_min {a = (S _)} {b = Z} {c = (S _)} (Stp _) _ impossible
two_to_min {a = (S _)} {b = (S _)} {c = Z} _ (E2Z _) impossible
two_to_min {a = (S _)} {b = (S _)} {c = Z} _ (Stp _) impossible
two_to_min {a = (S k)} {b = (S j)} {c = (S i)} (Stp x) (Stp y) = Stp (two_to_min x y)
 
two_to_max : STE a b -> STE c b -> STE (mmax a c) b
two_to_max {a = Z} {b = b} {c = c} p q = q
two_to_max {a = (S _)} {b = Z} {c = Z} (E2Z _) _ impossible
two_to_max {a = (S _)} {b = Z} {c = Z} (Stp _) _ impossible
two_to_max {a = (S _)} {b = Z} {c = (S _)} (E2Z _) _ impossible
two_to_max {a = (S _)} {b = Z} {c = (S _)} (Stp _) _ impossible
two_to_max {a = (S k)} {b = (S j)} {c = Z} p q = p
two_to_max {a = (S k)} {b = (S j)} {c = (S i)} (Stp x) (Stp y) = Stp (two_to_max x y)
 

insert : STree a b -> (e : Nat) -> STree (mmin a e) (mmax b e)
insert {a} Empt e = case order a e of
                         Left p => rewrite sym (maxFromP a e p) 
                                in rewrite sym (minFromP a e p) 
                                in (Fork Empt Empt e p (refl e) (refl a) (refl e))
                         Right p => let q = minFromP e a p
                                        s = maxFromP e a p
                                        t = maxKom a e
                                        r = minKom a e in 
                                        rewrite r in 
                                        rewrite t in
                                        rewrite sym q in 
                                        rewrite sym s in (Fork Empt Empt e (refl e) p (refl e) (refl a))
insert {a} {b} (Fork x y k z w f g ) e = case order k e of
                                         Left p => let (Fork o u i d s t r) = insert y e 
                                                       q = minFromP' (trans (trans f z) p)
                                                       qq= trans t (trans d (trans s r))
                                                   in rewrite sym q
                                                   in Fork x (Fork o u i d s t r) k z (two_to_min w p) f qq
                                         Right p => let (Fork o u i d s t r) = insert x e
                                                        q = maxFromP' (trans p (trans w g))
                                                        qq= trans t (trans d (trans s r))
                                                    in rewrite sym (maxKom e b)
                                                    in rewrite sym q
                                                    in Fork (Fork o u i d s t r) y k (two_to_max z p) w qq g

list_to_tree : List Nat -> (a : Nat ** b : Nat ** STree a b)
list_to_tree [] = (0 ** 0 ** Empt)
list_to_tree (x :: xs) = let (a ** b ** t) = list_to_tree xs 
                             t' = insert t x
                             in (mmin a x ** mmax b x ** t')
                             
                             
tree_to_list : STree a b -> List Nat
tree_to_list Empt = []
tree_to_list (Fork x y e z w s t) = tree_to_list x ++ [e] ++ tree_to_list y


sort : List Nat -> List Nat
sort l = let (a ** b ** t) = list_to_tree l
         in tree_to_list t
