module HetList

import Data.Vect

data HetList : List Type -> Type where
  N : HetList []
  C : (x : a) -> HetList ts -> HetList (a::ts)
  
  
ex : HetList [Nat, Nat, Double]
ex = C 1 (C 2 (C 3.0 N))

idx_l : Nat -> List Type -> Type
idx_l Z [] = ()
idx_l Z (x :: xs) = x
idx_l (S k) [] = ()
idx_l (S k) (x :: xs) = idx_l k xs

idx : (n : Nat) -> HetList ts -> HetList.idx_l n ts
idx Z N = ()
idx Z (C x y) = x
idx (S k) N = ()
idx (S k) (C x y) = idx k y 


ex_idx : Double
ex_idx = idx 2 ex



