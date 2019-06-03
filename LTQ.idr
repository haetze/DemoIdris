module LTQ 


data LTQ : (a : Nat) -> (b : Nat) -> Type where
  Base : (n : Nat) -> LTQ Z n
  Ind : (p : LTQ n m) -> LTQ (S n) (S m)
  
   
stmt_1 : LTQ (S n) m -> (x:Nat  ** m = S x)
stmt_1 {m = S x} p = (x ** Refl)
