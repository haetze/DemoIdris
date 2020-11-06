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

fromPropList : PropList a f -> List a
fromPropList [] = []
fromPropList (Cons x prf y) = x :: fromPropList y

hold : {a : Type} -> (g : a -> Bool) -> (x : a) -> (b : Bool ** b = g x)
hold g x = (g x ** Refl)

filter : PropList a f -> (g : a -> Bool) -> PropList a (\a => (f a) && (g a))
filter [] g = []
filter (Cons x prf y) g = let q = cong {f = \e => e && g x} prf
                          in case hold g x of
                            (True ** p) => Cons x (rewrite p in q) (filter y g)
                            (False ** p) => filter y g

filter' : List a -> (g : a -> Bool) -> PropList a g
filter' [] g = []
filter' (x :: xs) g = case hold g x of
                           (True ** p) => Cons x (sym p) (filter' xs g)
                           (False ** _) => filter' xs g

l : List Nat
l = [0,1,2,0,3,1]

any_list : PropList Nat (\n => True)
any_list = toPropList l 

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

zeros' : PropList Nat (\n => bin n && zero n)
zeros' = filter' l (\n => bin n && zero n)
