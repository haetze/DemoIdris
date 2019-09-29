module EvenOdd


data Even : Nat -> Type where
  EvenZeroP : Even Z
  EvenStepP : Even n -> Even (S (S n))
  
data Odd : Nat -> Type where
  OddOnesP : Odd (S Z)
  OddStepP : Odd n -> Odd (S (S n))


number_odd_or_even : (n : Nat) -> Either (Even n) (Odd n)
number_odd_or_even Z = Left EvenZeroP
number_odd_or_even (S Z) = Right OddOnesP
number_odd_or_even (S (S n)) = case number_odd_or_even n of
                                    Left p => Left (EvenStepP p)
                                    Right p => Right (OddStepP p) 
                               
                   
                   
                   
                               
