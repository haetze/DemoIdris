module GrowingH

fun_app : Nat -> (a -> a) -> a -> a
fun_app Z f a = a
fun_app (S n) f a = f (fun_app n f a)


f_0 : Nat -> Nat 
f_0 x = S x

stmt_2 : (x : Nat) -> f_0 x = S x
stmt_2 x = Refl

stmt_1 : (a : Nat) -> (b : Nat) -> fun_app a GrowingH.f_0 b = plus a b
stmt_1 Z b = Refl
stmt_1 (S k) b = let r = stmt_1 k b in cong r
                

f_1 : Nat -> Nat
f_1 n = fun_app n f_0 n

rew : (x : Nat) -> x + (x + 0) = x + x
rew x = rewrite plusZeroRightNeutral x in Refl

f_1_eq_times_2 : (x : Nat) -> S (S Z) * x = GrowingH.f_1 x
f_1_eq_times_2 Z = Refl
f_1_eq_times_2 (S k) = rewrite plusZeroRightNeutral k in 
                       rewrite stmt_1 k (S k) in Refl
 
