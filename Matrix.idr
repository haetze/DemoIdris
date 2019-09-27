module Matrix

data Vec : Nat -> Type -> Type where
  Nil  : Vec Z a
  (::) : a -> Vec n a -> Vec (S n) a


empties : (m : Nat) -> Vec m (Vec 0 a)
empties Z = []
empties (S k) = [] :: empties k

help : Vec m (Vec n a) -> Vec m a -> Vec m (Vec (S n) a)
help [] [] = []
help (z :: w) (x :: y) = (x :: z) :: help w y

transpose : {m : _} -> (mat : Vec n (Vec m a)) -> Vec m (Vec n a)
transpose {m} [] = empties m
transpose (x :: y) = let y_trans = transpose y 
                     in help y_trans x


test_mat : Vec 3 (Vec 2 Nat)
test_mat = [[1,2], [3,4], [5,6]]

test_mat' : Vec 2 (Vec 3 Nat)
test_mat' = transpose test_mat

test_mat'' : Vec 3 (Vec 2 Nat)
test_mat'' = transpose test_mat'

test_vec : Vec 1 (Vec 3 Nat)
test_vec = [[1,2,3]]

test_vec' : Vec 3 (Vec 1 Nat)
test_vec' = transpose test_vec

test_vec'' : Vec 1 (Vec 3 Nat)
test_vec'' = transpose test_vec'
 
