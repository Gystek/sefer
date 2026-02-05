module Utils ( allThree, pairs ) where

allThree :: (a -> b) -> (a, a, a) -> (b, b, b)
allThree f (x, y, z) = (f x, f y, f z)


pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = let mkp = (,) x
               in Prelude.map mkp xs ++ pairs xs
