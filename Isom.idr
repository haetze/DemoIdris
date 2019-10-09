module Isom



-- swap : (a, b) -> (b, a)
-- swap (a,b) = (b, a)

||| Proof that
||| A x B \cong B x A
swapRec : (a, b) = swap (swap (a, b))
swapRec = Refl


