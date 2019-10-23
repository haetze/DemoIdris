module Inv

import Data.Vect
     

s : Nat -> Nat
s x = S x

p : Nat -> Nat
p (Z) = Z
p (S x) = x

inv_p_s : (x : Nat) -> p (s x) = x
inv_p_s x = Refl

t : Vect (S n) a -> Vect n a
t (x :: xs) = xs

u : a -> Vect n a -> Vect (S n) a
u x xs = x :: xs

inv_t_u : (x : a) -> (xs : Vect n a) -> t (u x xs) = xs
inv_t_u x xs = Refl

inv_u_t : (xs : Vect (S n) a) -> u (head xs) (t xs) = xs
inv_u_t (x :: xs) = Refl

inv_id : a -> Prelude.Basics.id (Prelude.Basics.id a) = a
inv_id x = Refl

maps : (a -> b) -> List a -> List b
maps f [] = []
maps f (x :: xs) = f x :: maps f xs

head_eq : (x : a) 
       -> (y : a) 
       -> (xs : List a)
       -> (ys : List a) 
       -> x :: xs = y :: ys 
       -> x = y
head_eq y y [] [] Refl = Refl
head_eq _ _ [] (_ :: _) Refl impossible
head_eq _ _ (_ :: _) [] Refl impossible
head_eq y y (w :: ys) (w :: ys) Refl = Refl

tail_eq : (x : a) 
       -> (y : a) 
       -> (xs : List a)
       -> (ys : List a) 
       -> x :: xs = y :: ys 
       -> xs = ys
tail_eq y y [] [] Refl = Refl
tail_eq _ _ [] (_ :: _) Refl impossible
tail_eq _ _ (_ :: _) [] Refl impossible
tail_eq y y (w :: ys) (w :: ys) Refl = Refl

cons_eq : (x : a) 
       -> (y : a) 
       -> (xs : List a)
       -> (ys : List a)
       -> x = y 
       -> xs = ys 
       -> x :: xs = y :: ys
cons_eq y y [] [] Refl Refl = Refl
cons_eq _ _ [] (_ :: _) _ Refl impossible
cons_eq _ _ (_ :: _) [] _ Refl impossible
cons_eq y y (w :: ys) (w :: ys) Refl Refl = Refl

map_w_inv : (xs : List a)
         -> (ys : List b)
         -> (g : b -> a) 
         -> ys = maps f xs 
         -> ((x : a) -> g (f x) = x)
         -> xs = maps g ys
map_w_inv [] [] g p p_gen = Refl
map_w_inv [] (_ :: _) _ Refl _ impossible
map_w_inv (_ :: _) [] _ Refl _ impossible
map_w_inv {f} (x :: xs) (y :: ys) g p p_gen = 
              let hd_eq = head_eq y (f x) ys (maps f xs) p
                  hd_eq'= cong {f = g} hd_eq
                  inv_x = p_gen x
                  tl_eq = tail_eq y (f x) ys (maps f xs) p
                  recur = map_w_inv xs ys g tl_eq p_gen
                  r     = cons_eq (g (f x)) (g y) xs (maps g ys) (sym hd_eq') recur 
              in rewrite (sym inv_x) in r 

map_w_inv_id : (xs : List a)
            -> (ys : List a)
            -> ys = maps Prelude.Basics.id xs 
            -> xs = maps Prelude.Basics.id ys
map_w_inv_id xs ys p = map_w_inv {f = id} xs ys id p (\x => Refl)
