module Pred

test : LT 0 12
test = LTESucc LTEZero


pred : LT 0 n -> (m ** n = S m)
pred _ {n = Z} impossible
pred _ {n = S k} = (k ** Refl)
