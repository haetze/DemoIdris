module BuchTestView1 

data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])
  
snocListHelp :  (snoc : SnocList input) 
             -> (rest : List a) 
             -> SnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite appendNilRightNeutral input in snoc 
snocListHelp {input} snoc (x::xs) = rewrite appendAssociative input [x] xs in snocListHelp (Snoc snoc {x}) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
  isSuffix [] input2 | Empty = True
  isSuffix (xs ++ [x]) input2 | (Snoc rec) with (snocList input2)
    isSuffix (xs ++ [x]) [] | (Snoc rec) | Empty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc rec) | (Snoc z)
      = if x == y then isSuffix xs ys | rec | z
                  else False --          ^    ^
                             --          |    |
                             --          |  ysrec in Book
                             --          xsrec in Book
