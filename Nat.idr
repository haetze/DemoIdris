module Nat


stmt_1 : S (n + m) = n + (S m)
stmt_1 {n = Z} = Refl
stmt_1 {n = S k} {m} = let rec = stmt_1 {n = k} {m}
                       in cong {f = S} rec 

stmt_3 : (n : Nat) -> n + n = n + (n + 0)
stmt_3 n = rewrite plusCommutative n 0 in Refl

stmt_2 : (n : Nat) -> n + n = 2 * n
stmt_2 n = rewrite stmt_3 n in Refl 
