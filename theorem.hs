data Void

triple_implies_simple :: (((a -> Void) -> Void) -> Void) -> (a -> Void)
triple_implies_simple f x = f (\g -> g x)
