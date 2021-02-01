module Reverse2
import Data.Vect

snoc : Vect n a -> a -> Vect (S n) a
snoc [] x = [x]
snoc (y :: xs) x = y :: snoc xs x

data IsRev : Vect n a -> Vect n a -> Type where
  Empty : IsRev [] []
  AddElement : (x : a) -> IsRev xs ys -> IsRev (x::xs) (snoc ys x)



rev : (xs : Vect n a) -> (ys : Vect n a ** IsRev xs ys)
rev [] = ([] ** Empty)
rev (x :: xs) = let (ys ** p) = rev xs in (snoc ys x ** AddElement x p)

lem : (xs : Vect n a)
      ->(ys : Vect n a)
      ->(x : a)
      ->IsRev xs ys
      ->IsRev (snoc xs x) (x::ys)
lem [] [] x Empty = AddElement x Empty
lem (y :: xs) (snoc zs y) x (AddElement y z) = 
  let p = lem xs zs x z
  in AddElement y p

stmt_1 : IsRev xs ys -> IsRev ys xs
stmt_1 Empty = Empty
stmt_1 {xs = x::xs'} {ys = snoc ys' x} (AddElement x p) = 
  let p_1 = stmt_1 p
  in lem ys' xs' x p_1

stmt_2 : IsRev xs ys -> IsRev xs zs -> ys = zs
stmt_2 Empty Empty = Refl
stmt_2 (AddElement x y) (AddElement x z) = 
  let p_1 = stmt_2 y z
  in rewrite p_1 in Refl

stmt_3 : IsRev xs ys -> IsRev ys zs -> xs = zs
stmt_3 p q = 
  let p_1 = stmt_1 p
      p_2 = stmt_2 p_1 q
  in p_2
