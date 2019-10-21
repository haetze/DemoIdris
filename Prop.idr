module Prop


conc : (b -> c) -> (a -> b) -> a -> c
conc g f a = g (f a)


conc_assoc : (h : c -> d) 
          -> (g : b -> c) 
          -> (f : a -> b) 
          -> (x : a) 
          -> ((conc h (conc g f)) x) = ((conc (conc h g) f) x)
conc_assoc h g f x = Refl

id_neutr : (x : a) -> id x = x
id_neutr x = Refl
      
conc_id_neutr : (h : a -> b) -> (x : a) -> (conc h Prelude.Basics.id) x = h x
conc_id_neutr h x = Refl

conc_id_neutr_2 : (h : a -> b) -> (x : a) -> (conc Prelude.Basics.id h) x = h x
conc_id_neutr_2 h x = Refl

mapL : (a -> b) -> List a -> List b
mapL f [] = []
mapL f (x::xs) = f x :: mapL f xs

addHead : (x : a) -> (xs : List a) -> List a
addHead x xs = x :: xs

map_id_neutr : (l : List a) -> mapL Prelude.Basics.id l = l
map_id_neutr [] = Refl
map_id_neutr (x :: xs) = cong {f = addHead x} (map_id_neutr xs) 
