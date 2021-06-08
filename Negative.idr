module Negative

data T : Type where
  C : T
  X : (a : T) -> (f : T -> Nat) -> T
--                         ^
--                  Is neither positive nor half-positive
--             https://en.wikipedia.org/wiki/Induction-recursion                         
-- 
