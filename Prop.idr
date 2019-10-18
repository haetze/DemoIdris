module Prop


conc : (b -> c) -> (a -> b) -> a -> c
conc g f a = g (f a)


conc_assoc : (h : c -> d) 
          -> (g : b -> c) 
          -> (f : a -> b) 
          -> (x : a) 
          -> ((conc h (conc g f)) x) = ((conc (conc h g) f) x)
conc_assoc h g f x = Refl

      
