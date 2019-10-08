module EvenOdd


data Even : Nat -> Type where
  EvenZeroP : Even Z
  EvenStepP : Even n -> Even (S (S n))
  
data Odd : Nat -> Type where
  OddOnesP : Odd (S Z)
  OddStepP : Odd n -> Odd (S (S n))


||| Proof that
||| \forall n \in N. n is even or n is odd
number_odd_or_even : (n : Nat) -> Either (Even n) (Odd n)
number_odd_or_even Z = Left EvenZeroP
number_odd_or_even (S Z) = Right OddOnesP
number_odd_or_even (S (S n)) = case number_odd_or_even n of
                                    Left p => Left (EvenStepP p)
                                    Right p => Right (OddStepP p) 
                               
||| Proof that
||| \forall n, m \in N. S (n + m) = n + (S m)
stmt_1 :                S (n + m) = n + (S m)
stmt_1 {n = Z} = Refl
stmt_1 {n = S k} {m} = let rec = stmt_1 {n = k} {m}
                       in cong {f = S} rec 

pred : (n : Nat) -> Nat
pred Z = Z
pred (S n) = n


stmt_3 : S n = S (k + S k) -> n = k + S k
stmt_3 = cong {f = EvenOdd.pred}

stmt_4 : S (k + S k) = S k + S k
stmt_4 = Refl

stmt_5 : S (S k + k) = S k + S k
stmt_5 {k} = rewrite plusCommutative {left = S k} {right = k} in stmt_4

stmt_6 : S n = S k + S k -> S n = S (k + S k)
stmt_6 {n} {k} p = p

stmt_7 : S n = S k + S k -> n = k + S k
stmt_7 p = stmt_3 (stmt_6 p)

stmt_8 : S n = S k + S k -> n = S k + k
stmt_8 {k} p = rewrite plusCommutative {left = S k} {right = k} in stmt_7 p

stmt_9 : S (S n) = S k + S k -> S n = S k + k
stmt_9 {n} {k} p = stmt_8 {n = S n} {k = k} p

stmt_10 : S n = S k + k -> n = k + k
stmt_10 {n} {k} p = cong {f = EvenOdd.pred} p

stmt_11 : S (S n) = S k + S k -> n = k + k
stmt_11 p = let r = stmt_9 p in stmt_10 r 

stmt_12 : S (S n) = S (S k + S k) -> n = S (k + k)
stmt_12 {k} p = let r = cong {f = EvenOdd.pred} p 
                    r' = stmt_7 r 
            in rewrite stmt_1 {n = k} {m = k} in r'

||| Proof that 
||| \forall n' . n' is even => \forall n. n' = S (n + n) => False
stmt_2 : Even m -> (n : Nat) -> m = S (n + n) -> Void
stmt_2 {m = Z} EvenZeroP Z Refl impossible
stmt_2 {m = Z} EvenZeroP (S _) Refl impossible
stmt_2 (EvenStepP _) Z Refl impossible
stmt_2 (EvenStepP x) (S k) p = let rec = stmt_2 x k (stmt_12 p) in rec
                   
plus_Z : plus n Z = n
plus_Z {n = Z} = Refl
plus_Z {n = S k} = let r = plus_Z {n = k} 
                   in cong r

distr : S n = S (m + m) -> S n = m + S m
distr {m} p = rewrite sym (stmt_1 {n = m} {m = m}) in p

                                                         
add_two : n = m + m -> S (S n) = S m + S m
add_two {m} p = let r = cong {f = S} p
                    s = distr r 
                    t = cong {f = S} s
            in t

lem_3 : S (S Z) * n = n + n
lem_3 {n} = rewrite sym (plus_Z {n = n}) in Refl

lem_4 : (\x1 => n = (S (S Z)) * x1) x -> (\x1 => n = x1 + x1) x
lem_4 {x} p = rewrite sym (lem_3 {n = x}) in p

lem_2 : (x ** n = (S (S Z)) * x) -> (x ** n = x + x)                                      
lem_2 (x ** p) = let q = lem_4 p
                 in (x ** q)


lem_6 : plus y y = plus y (plus y Z)
lem_6 {y} = rewrite plus_Z {n = y} in Refl

lem_7 : S (S n) = m + m -> S (S n) = m + (plus m Z)
lem_7 {m} p = rewrite sym (lem_6 {y = m}) in p
                                                                                             
||| Proof that
||| \forall n. n is even => \exists x. n = 2 * x
even_mult_2 : Even n -> (x ** n = S (S Z) * x)
even_mult_2 EvenZeroP = (0 ** Refl)
even_mult_2 (EvenStepP x) = let r = even_mult_2 x
                                (y ** p)  = lem_2 r
                                q = add_two p
                                w = lem_7 q
                            in (S y ** w)
 
