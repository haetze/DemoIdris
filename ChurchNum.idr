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

mult_c : (x : (a -> a) -> a -> a)
      -> (y : (a -> a) -> a -> a)
      -> (a -> a)
      -> a
      -> a
mult_c x y s = x (y s)

stmt_3 : (n : Nat)
      -> (f : a -> a)
      -> (x : a)
      -> ChurchNum.c n f (f x) = f (ChurchNum.c n f x)
stmt_3 Z f x = Refl
stmt_3 (S k) f x = let r = stmt_3 k f x in cong r

stmt_2 : (n : Nat) 
      -> (m : Nat)
      -> (m': Nat)
      -> (l : Nat)
      -> (f : a -> a)
      -> (x : a)
      -> ChurchNum.c m' f (ChurchNum.c m f x) = ChurchNum.c n f x
      -> ChurchNum.c m' f (ChurchNum.c (plus l m) f x) = ChurchNum.c (plus l n) f x
stmt_2 n m m' Z f x p = p
stmt_2 n m m' (S k) f x p = let r = stmt_2 n m m' k f x p 
                                s = cong {f = f} r
                                t = stmt_3 m' f (c (plus k m) f x) 
                            in rewrite t in s

stmt_1 : (n : Nat) 
      -> (m : Nat)
      -> (f : a -> a)
      -> (x : a)
      -> ChurchNum.c m f (ChurchNum.c (mult n m) f x) = ChurchNum.c (plus m (mult n m)) f x
stmt_1 Z m f x = rewrite plusZeroRightNeutral m in Refl
stmt_1 (S k) m f x = let r = stmt_1 k m f x 
                         s = stmt_2 (plus m (mult k m)) (mult k m) m m f x r
                     in s

prop' : (n : Nat) 
     -> (m : Nat)
     -> (f : a -> a)
     -> (x : a)
     -> ChurchNum.mult_c (ChurchNum.c n) (ChurchNum.c m) f x = ChurchNum.c (mult n m) f x
prop' Z m f x = Refl
prop' (S k) m f x = let r = prop' k m f x 
                        s = cong {f = c m f} r
                        t = stmt_1 k m f x
                        u = trans s t 
                    in u


