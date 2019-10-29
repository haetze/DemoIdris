module ChurchNum

||| Applies a f function n times to a value x
||| Domain and Codomain of the function need to be identical
c : Nat -> (a -> a) -> a -> a
c Z f a = a
c (S k) f a = f (c k f a)


||| Church numeral for 0
c_0 : (a -> a) -> a -> a
c_0 = c Z


add : (x : (a -> a) -> a -> a)
   -> (y : (a -> a) -> a -> a)
   -> (a -> a)
   -> a
   -> a
add x y s z = x s (y s z)

   
prop : (n : Nat) 
    -> (m : Nat)
    -> (f : a -> a)
    -> (x : a)
    -> ChurchNum.add (ChurchNum.c n) (ChurchNum.c m) f x = ChurchNum.c (plus n m) f x
prop Z m f x = Refl
prop (S k) m f x = cong (prop k m f x)
