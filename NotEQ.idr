module NotEQ

data NotEQNat : Nat -> Nat -> Type where
  BaseZS : NotEQNat Z (S n)
  BaseSZ : NotEQNat (S n) Z
  Step   : NotEQNat n m -> NotEQNat (S n) (S m)
  
  
||| Proof that
||| 4 =/= 2
stmt_1 : NotEQNat 4 2
stmt_1 = Step (Step BaseSZ)


||| Proof that
||| 2 =/= 2 is not possible
stmt_2 : NotEQNat 2 2 -> Void
stmt_2 (Step (Step BaseZS)) impossible
stmt_2 (Step (Step BaseSZ)) impossible
stmt_2 (Step (Step (Step _))) impossible

