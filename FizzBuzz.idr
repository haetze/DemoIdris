module FizzBuzz

import Data.Vect

data State : Type where
  Fizz : State
  Buzz : State
  FizzBuzz : State
  None : Nat -> State
  
  

nat2state : Nat -> State
nat2state k = 
  case (mod k 3, mod k 5) of
    (Z,Z) => FizzBuzz
    (_,Z) => Buzz
    (Z,_) => Fizz
    (_,_) => None k

vect : Vect n Nat
vect {n = Z} = []
vect {n = (S k)} = S k :: vect {n = k}

fizzbuzz_game : Vect n Nat -> Vect n State
fizzbuzz_game = map nat2state 
