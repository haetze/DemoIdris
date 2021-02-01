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

lem_1 : snoc [] x = [x]
lem_1 = Refl

lem_2 : snoc ys x = [x] -> ys = []
lem_2 {ys = []} p = Refl

lem_3_1 : IsRev [x] [z] -> [z] = snoc [] z
lem_3_1 p = Refl 

lem_3_2 : IsRev (snoc [] x) [z] -> [x] = snoc [] x
lem_3_2 p = Refl 

lem_4 : IsRev [x] [z] -> IsRev [x] (snoc [] z)
lem_4 p = p

lem_5 : IsRev [x] (snoc [] z) -> x = z
lem_5 Empty impossible
lem_5 (AddElement x Empty) = Refl

lem_6 : (xs : Vect (S n) a) 
      ->(ys : Vect n a)
      ->(x : a)
      ->IsRev (snoc ys x) xs 
      ->(xs' : Vect n a ** (x :: xs') = xs)
lem_6 (snoc [] x) [] x (AddElement x Empty) = ([] ** Refl)
lem_6 (snoc xs y) (y :: ys) x (AddElement y p) = 
  let (xs' ** p_1) = lem_6 xs ys x p
  in rewrite sym p_1 in (snoc xs' y ** Refl)
  
lem_7 : (xs : Vect n a)
      ->(ys : Vect n a)
      ->(x : a)
      ->IsRev xs ys
      ->IsRev (snoc xs x) (x::ys)
lem_7 [] [] x Empty = AddElement x Empty
lem_7 (y :: xs) (snoc zs y) x (AddElement y z) = 
  let p = lem_7 xs zs x z
  in AddElement y p

stmt_1 : IsRev xs ys -> IsRev ys xs
stmt_1 Empty = Empty
stmt_1 {xs = x::xs'} {ys = snoc ys' x} (AddElement x p) = 
  let p_1 = stmt_1 p
  in lem_7 ys' xs' x p_1

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
