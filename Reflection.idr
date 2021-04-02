module Reflection


data Exp : Type where
  Ident : Exp
  Vr   : Nat -> Exp
  Op    : Exp -> Exp -> Exp

interprete : Exp -> Nat
interprete Ident = 0
interprete (Vr k) = k
interprete (Op x y) = interprete x + interprete y

to_list : Exp -> List Nat
to_list Ident = []
to_list (Vr k) = [k]
to_list (Op x y) = to_list x ++ to_list y

interprete_list : List Nat -> Nat
interprete_list [] = 0
interprete_list (x :: xs) = x + interprete_list xs


to_list_correct : (x : List Nat) -> (y : List Nat) -> interprete_list x + interprete_list y = interprete_list (x ++ y)
to_list_correct [] y = Refl
to_list_correct (x :: xs) y = let p = to_list_correct xs y
                                  q = plusAssociative x (interprete_list xs) (interprete_list y)
                              in rewrite (sym p)
                              in rewrite q
                              in Refl


to_list_correct_2 : (e : Exp) -> interprete e = interprete_list (to_list e)
to_list_correct_2 Ident = Refl
to_list_correct_2 (Vr k) = let p = plusZeroRightNeutral k in sym p
to_list_correct_2 (Op x y) = let p_1 = to_list_correct_2 x
                                 p_2 = to_list_correct_2 y
                                 p_3 = to_list_correct (to_list x) (to_list y)
                             in rewrite p_1
                             in rewrite p_2
                             in rewrite p_3
                             in Refl


m_reflect : (e : Exp) -> 
       (f : Exp) -> 
       interprete_list (to_list e) = interprete_list (to_list f) ->
       interprete e = interprete f
m_reflect e f p = 
  let q_1 = to_list_correct_2 e 
      q_2 = to_list_correct_2 f
  in rewrite q_1
  in rewrite q_2
  in p
     
