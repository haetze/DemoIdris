module Sort


data LTQ : (a : Nat) -> (b : Nat) -> Type where
  Zero : (b : Nat) -> LTQ Z b 
  Step : (a : Nat) -> (b : Nat) -> LTQ a b -> LTQ (S a) (S b)


lessthanproof_1_lt_2 : LTQ 1 2
lessthanproof_1_lt_2 = Step 0 1 (Zero 1)

lessthanproof_3_lt_5 : LTQ 3 5
lessthanproof_3_lt_5 = Step 2 4 (Step 1 3 (Step 0 2 (Zero 2)))

non_sense : (a : Nat) -> (b : Nat) -> LTQ a b
non_sense Z b = Zero b
non_sense (S k) Z = ?undefineable
non_sense (S k) (S j) = Step k j (non_sense k j)




