module Sort2 


import Data.Vect

data Contained : (a : Nat) -> (v : Vect (S n) Nat) -> Type where
  BaseC : (a : Nat) -> Contained a [a]
  AddC : (x : Nat) -> (p : Contained a v) -> Contained a (x :: v)
  
data ContainedAll : (v : Vect n Nat) -> (u : Vect m Nat) -> Type where
  BaseCA : (u : Vect m Nat) -> ContainedAll [] u 
  AddCA : (x : Nat) -> (p : Contained x u) -> (q : ContainedAll v u) -> ContainedAll (x :: v) u 

data LTQ : (a : Nat) -> (b : Nat) -> Type where
  Zero : (b : Nat) -> LTQ 0 a
  Step : LTQ a b -> LTQ (S a) (S b)

data SVect : (s : Vect (S m) Nat) -> (v : Vect (S n) Nat) -> Type where
  Introduce : (h : Nat) -> (v : Vect (S n) Nat) -> (p : Contained h v) -> SVect [h] v
  Add : (new : Nat) -> (sv : SVect (h :: s) v) -> (p : LTQ new h) -> (q : Contained new v) -> SVect (new :: h :: s) v 


