module Record


data Contained : (x : a) -> List a -> Type where
  Base : Contained x (x::xs)
  Add : Contained x xs -> Contained x (y::xs)
  
  
  
  
five_list : Contained 5 [1,2,3,4,5]
five_list = Add (Add (Add (Add Base)))


data Record : (v : Type) -> (keys : List k) -> Type where
  EmptyR : Record v []
  AddR : (x : v) ->  (y : k) -> Record v keys -> Record v (y::keys)


sqs : Record Nat [1,2,3,4,5]
sqs = AddR 1 1 (AddR 4 2 (AddR 9 3 (AddR 16 4 (AddR 25 5 EmptyR))))

get_v : Record v keys -> Contained key keys -> v
get_v {key = key} (AddR x key y) Base = x
get_v {key = key} (AddR _ y z) (Add x) = get_v z x



 
