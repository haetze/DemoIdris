module MList

data MList : Type -> Type where
  N : MList a
  C : a -> MList a -> MList a
  
  
mlist_2_list : MList a -> List a
mlist_2_list N = []
mlist_2_list (C x y) = x :: mlist_2_list y


list_2_mlist : List a -> MList a
list_2_mlist [] = N
list_2_mlist (x :: xs) = C x (list_2_mlist xs)


list_eq_mlist : (xs : List a) -> (ys ** xs = mlist_2_list ys)
list_eq_mlist [] = (N ** Refl)
list_eq_mlist (x :: xs) = let (ys ** p) = list_eq_mlist xs 
                          in (C x ys ** cong {f = \l=>x :: l} p)
                          
mlist_eq_list : (xs : MList a) -> (ys ** xs = list_2_mlist ys)
mlist_eq_list N = ([] ** Refl)
mlist_eq_list (C x y) = let (ys ** p) = mlist_eq_list y
                        in (x :: ys ** cong {f = \l=>C x l} p)
                        
                        
