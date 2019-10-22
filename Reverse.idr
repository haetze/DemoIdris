module Reverse 

app : List a -> List a -> List a
app [] ys = ys
app (x :: xs) ys = x :: app xs  ys

data SnocList : {a : Type} -> (List a) -> Type where
  Empty : SnocList []
  Snoc : SnocList xs -> (x : a) -> SnocList (xs ++ [x])
  
  
reverseSnoc : SnocList {a} l -> List a
reverseSnoc Empty = []
reverseSnoc (Snoc y x) = x :: reverseSnoc y

snocHelp : (snoc : SnocList input) 
        -> (rest : List a)
        -> SnocList (input ++ rest)
snocHelp {input} snoc [] = rewrite appendNilRightNeutral input in snoc 
snocHelp {input} snoc (x :: xs) = rewrite appendAssociative input [x] xs 
                                  in snocHelp (Snoc snoc x) xs        


snocList : (l : List a) -> SnocList l
snocList = snocHelp Empty

reverseHelp : (l : List a) -> (snoc : SnocList l) -> List a
reverseHelp [] Empty = []
reverseHelp (xs ++ [x]) (Snoc y x) = x :: reverseHelp xs y

rev : List a -> List a
rev l = reverseHelp l (snocList l)


data IsRevOf : List a -> List a -> Type where
  EmptyRev : IsRevOf [] []
  ConsRev : (x: a) -> (l : IsRevOf ys xs) -> IsRevOf (app ys [x]) (x::xs)
  --SnocRev : (x: a) -> (l : IsRevOf ys xs) -> IsRevOf (x :: ys) (app xs [x])
  
example_1 : IsRevOf [3] [3]  
example_1 = ConsRev 3 EmptyRev

example_2 : IsRevOf [3,2] [2,3]  
example_2 = ConsRev 2 example_1


rev' : (xs : List a) -> (ys ** IsRevOf ys xs)
rev' [] = ([] ** EmptyRev)
rev' (x::xs) = let (ys' ** p)  = rev' xs in (app ys' [x] ** ConsRev x p)

m_rev : (xs : List a) -> List a
m_rev [] = []
m_rev (x :: xs) = app (m_rev xs) [x]



m_rev_Rev : (xs : List a) -> IsRevOf (m_rev xs) xs
m_rev_Rev [] = EmptyRev
m_rev_Rev (x :: xs) = ConsRev x (m_rev_Rev xs) 

cons_append : (x : a) -> (y : a) -> (xs : List a) -> x :: app xs [y] = app (x::xs) [y]
cons_append x y xs = Refl



append_rev : (x : a) -> (xs : List a) -> x :: m_rev xs = m_rev (app xs [x])
append_rev x [] = Refl
append_rev x (y :: xs) = let r = append_rev x xs in cong {f = \l => app l [y]} r

stmt_1 : (xs : List a) -> IsRevOf ys xs -> ys = m_rev xs
stmt_1 [] EmptyRev = Refl
stmt_1 (x :: xs) (ConsRev x y) = let r = stmt_1 xs y in cong {f = \l => app l [x]} r

rev_un : (xs : List a) -> (p: IsRevOf ys xs) -> (q : IsRevOf zs xs) -> zs = ys
rev_un [] EmptyRev EmptyRev = Refl
rev_un (_ :: _) (ConsRev _ _) EmptyRev impossible
rev_un (x :: ys) (ConsRev x yp) (ConsRev x yq) = let r = rev_un ys yp yq 
                                                 in cong {f = \l => app l [x]} r

lem : (x : a) -> (xs : List a) -> app xs [x] = [] -> Void
lem _ [] Refl impossible
lem _ (_ :: _) Refl impossible


help : app xs [x] = m_rev (x::ys) -> IsRevOf (app xs [x]) (x::ys) -> IsRevOf (m_rev (x::ys)) (x::ys)
help p q = rewrite sym p in q

help' : IsRevOf ys xs -> IsRevOf (m_rev xs) (m_rev ys) 
help' EmptyRev = EmptyRev
help' {ys = app ys [x]} (ConsRev x l) = let r = help' l 
                                            s = ConsRev x r 
                                            t = append_rev x ys
                                        in rewrite sym t in s


help'' : IsRevOf (m_rev (x :: ys)) (x :: ys) 
      -> m_rev (x :: ys) = m_rev (m_rev (m_rev (x :: ys)))
      -> IsRevOf (m_rev (m_rev (m_rev (x :: ys)))) (x :: ys)
help'' p q = rewrite sym q in p      

help''' : IsRevOf (m_rev xs) xs 
       -> m_rev xs = m_rev (m_rev ys) 
       -> IsRevOf (m_rev (m_rev ys)) xs
help''' p q = rewrite sym q in p        

revs_inv : IsRevOf ys xs -> ys = m_rev (m_rev ys) 
revs_inv {xs} {ys} p = let q = help' p
                           r = help' q
                           s = m_rev_Rev xs 
                           u = help' s
                           w = rev_un (m_rev (m_rev xs)) r u
                           v = help''' {xs = xs} {ys = ys} s w
                           result = rev_un xs v p 
                       in result


