module Nat


stmt_1 : S (n + m) = n + (S m)
stmt_1 {n = Z} = Refl
stmt_1 {n = S k} {m} = let rec = stmt_1 {n = k} {m}
                       in cong {f = S} rec 

stmt_3 : (n : Nat) -> n + n = n + (n + 0)
stmt_3 n = rewrite plusCommutative n 0 in Refl

stmt_2 : (n : Nat) -> n + n = 2 * n
stmt_2 n = rewrite stmt_3 n in Refl 

stmt_5 : n + (S m) = S (n + m) 
stmt_5 = sym stmt_1

add : Nat -> Nat -> Nat
add Z y = y
add (S k) y = S (add k y)

stmt_4 : (left : Nat) -> (right : Nat) -> left + right = right + left
stmt_4 Z Z = Refl
stmt_4 Z (S k) = cong (stmt_4 Z k)
stmt_4 (S k) right = rewrite stmt_5 {n = right} {m = k} in cong (stmt_4 k right)


stmt_6 : (x : Nat) -> (y : Nat) -> add x y = x + y
stmt_6 Z y = Refl
stmt_6 (S k) y = cong (stmt_6 k y)
