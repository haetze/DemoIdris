module PropList


data PropList : (a : Type) -> (a -> Bool) -> Type where
  Nil : PropList a f
  Cons : {a : Type} -> 
         {f : a -> Bool} -> 
         (x : a) -> 
         f x = True -> 
         PropList a f -> PropList a f
  
  
toPropList : List a -> PropList a (\x => True)
toPropList [] = []
toPropList (x :: xs) = Cons x Refl (toPropList xs)

hold : {a : Type} -> (g : a -> Bool) -> (x : a) -> (b : Bool ** b = g x)
hold g x = (g x ** Refl)

filter : PropList a f -> (g : a -> Bool) -> PropList a (\a => (f a) && (g a))
filter [] g = []
filter (Cons x prf y) g = let q = cong {f = \e => e && g x} prf
                          in case hold g x of
                            (True ** p) => Cons x (rewrite p in q) (filter y g)
                            (False ** p) => filter y g

any_list : PropList Nat (\n => True)
any_list = toPropList [0,1,2,0,3,1]

bin : Nat -> Bool
bin Z = True
bin (S Z) = True
bin _ = False

one_or_zero_list : PropList Nat PropList.bin
one_or_zero_list = filter any_list bin

zero : Nat -> Bool
zero Z = True
zero _ = False

zeros : PropList Nat (\n => bin n && zero n)
zeros = filter one_or_zero_list zero
