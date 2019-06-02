module Sort2 


import Data.Vect

data Contained : (a : Nat) -> (v : Vect (S n) Nat) -> Type where
  BaseC : (a : Nat) -> Contained a [a]
  AddC : (x : Nat) -> (p : Contained a v) -> Contained a (x :: v)
  
data ContainedAll : (v : Vect n Nat) -> (u : Vect m Nat) -> Type where
  BaseCA : (u : Vect m Nat) -> ContainedAll [] u 
  AddCA : (x : Nat) -> (p : Contained x u) -> (q : ContainedAll v u) -> ContainedAll (x :: v) u 

data LTQ : (a : Nat) -> (b : Nat) -> Type where
  Zero : (b : Nat) -> LTQ 0 a
  Step : LTQ a b -> LTQ (S a) (S b)

data SVect : (n : Nat)  -> (v : Vect (S m) Nat) -> (h : Nat) -> Type where
  Introduce : (h : Nat) -> (v : Vect (S n) Nat) -> (p : Contained h v) -> SVect (S Z) v h 
  Add : (new : Nat) -> (sv : SVect (S m) v h) -> (p : LTQ new h) -> (q : Contained new v) -> SVect (S (S m)) v new 

mini : (x : Nat) -> (y : Nat) -> Nat
mini Z y = Z
mini x Z = Z
mini (S k) (S j) = S (mini k j)
  
min : Vect (S n) Nat -> Nat
min (x :: []) = x
min (x :: ys@(y :: xs)) = mini x (min ys)


stmt_1 : (v : Vect (S Z) Nat) -> (u : Vect (S n) Nat) -> ContainedAll v u -> Contained (head v) u
stmt_1 [x] u (AddCA x p q) = p

stmt_2 : Data.Vect.head [x] = x
stmt_2 = Refl            

stmt_3 : Contained (Data.Vect.head [x]) u -> Contained x u
stmt_3 p = p

stmt_4 : (a : Nat) -> (b : Nat) -> Either (LTQ a b) (LTQ b a)
stmt_4 Z b = Left (Zero b)
stmt_4 a Z = Right (Zero a) 
stmt_4 (S k) (S j) = case stmt_4 k j of 
                     Left p => Left (Step p)
                     Right p => Right (Step p)

insert : (x : Nat) -> (v : SVect (S m) u h) -> (p : Contained x u) -> Either (SVect (S (S m)) u x) 
                                                                             (SVect (S (S m)) u h)
insert x (Introduce h u y) p = let q = stmt_4 x h in 
                               case q of 
                               Left q' => Left (Add x (Introduce h u y) q' p)
                               Right q' => Right (Add h (Introduce x u p) q' y)
insert x (Add h sv y q) p = let r = stmt_4 x h in 
                            case r of 
                            Left q' => Left (Add x (Add h sv y q) q' p)
                            Right q' => let s = insert x sv p in 
                                        case s of 
                                        Left (Add x' sv' p' q'') => Right (Add h (Add x' sv' p' q'') q' q)
                                        Right (Add h1 sv' p' q'') => Right (Add h (Add h1 sv' p' q'') y q)


stmt_6 : (x : Nat) -> mini x Z = Z
stmt_6 Z = Refl
stmt_6 (S k) = Refl 

stmt_8 : (p : LTQ x y) -> mini x y = x
stmt_8 (Zero b) = Refl
stmt_8 (Step x) = cong (stmt_8 x)

stmt_9 : min [j, k] = mini j k
stmt_9 = Refl

stmt_10 : (q : LTQ n b) -> (p : LTQ (S n) m) -> m = S b 
stmt_10 (Zero b) (Step x) = ?h_4
stmt_10 (Step y) (Step x) = ?h_3 

stmt_7 : (x : Nat) -> LTQ x (min v) -> LTQ x (min (x::v))
stmt_7 {v = Z :: []} Z (Zero b) =  Zero Z
stmt_7 {v = (S k) :: []} Z p =  Zero Z
stmt_7 {v = (S k) :: []} (S j) (Step x) = let r = stmt_8 x 
                                              s = stmt_7 {v = k :: []} j x in Step s 
stmt_7 {v = y :: ys} Z p = Zero Z
stmt_7 {v = y :: ys} (S k) p  = ?h3_2

stmt_5 : (x : Nat) -> (v : Vect (S n) Nat) -> LTQ (min (x::v)) x
stmt_5 Z (y :: []) = Zero Z
stmt_5 x (Z :: []) = rewrite stmt_6 x in Zero Z 
stmt_5 (S k) ((S j) :: []) = let r = stmt_5 k [j] in Step r
stmt_5 Z (y :: (z :: xs)) = Zero Z
stmt_5 (S k) (Z :: (z :: xs)) = Zero (S k)
stmt_5 (S k) ((S j) :: (z :: xs)) = let r = stmt_5 (S k) (z::xs) in ?p 
            
sort' : (v : Vect (S m) Nat) -> (u : Vect (S n) Nat) -> ContainedAll v u -> SVect (S m) u (min v)
sort' (x :: []) u p = let p' = stmt_1 [x] u p
                          q  = stmt_3 p' in (Introduce x u q)
sort' (x :: (y :: xs)) u (AddCA x p q) = let r = sort' (y::xs) u q 
                                             s = insert x r p in 
                                         case s of 
                                         Left s' => ?h
                                         Right s' => ?g  
                                         

