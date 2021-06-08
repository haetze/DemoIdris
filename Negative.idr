module Negative

data T : Nat -> Type where
  C : T a
  X : (a : T x) -> (f : T x -> Nat) -> T (S (f a))
--                         ^
--                  Is neither positive nor half-positive
--             https://en.wikipedia.org/wiki/Induction-recursion                         

