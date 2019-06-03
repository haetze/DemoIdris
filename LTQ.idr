module LTQ 


data LTQ : (a : Nat) -> (b : Nat) -> Type where
  Base : (n : Nat) -> LTQ Z n
  Ind : (p : LTQ n m) -> LTQ (S n) (S m)
  

||| Proof that 
||| \forall n,m\in N. (n + 1 <= m) => 
|||                    (\exists x\in N. x+1 = m)
stmt_1 : LTQ (S n) m -> (x:Nat  ** m = S x)
stmt_1 {m = S x} p = (x ** Refl)
