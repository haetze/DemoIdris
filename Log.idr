module Log



dis : (Either a b -> Void) -> (a -> Void, b -> Void)
dis f = (\a => f (Left a), \b => f (Right b))


dis_rev : (a -> Void, b -> Void) -> Either a b -> Void
dis_rev (f, g) (Left l) = f l
dis_rev (f, g) (Right r) = g r


revs : (r : Either a b) -> (f : Either a b -> Void) -> dis_rev (dis f) r = f r 
revs (Left l) f = Refl
revs (Right r) f = Refl


