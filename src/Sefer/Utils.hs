module Sefer.Utils ( allThree, both, pairs, pairs2, map1 ) where

map1 :: (a -> b) -> (a, c) -> (b, c)
map1 f (x, y) = (f x, y)

both :: (a -> b) -> (a, a) -> (b, b)
both f (x, y) = (f x, f y)

allThree :: (a -> b) -> (a, a, a) -> (b, b, b)
allThree f (x, y, z) = (f x, f y, f z)

pairs2 :: [a] -> [a] -> [(a, a)]
pairs2 [] _ = []
pairs2 (x:xs) ys = genPairs x ys ++ pairs2 xs ys
  where genPairs :: a -> [a] -> [(a, a)]
        genPairs _ [] = []
        genPairs x (y:ys) = (x, y) : genPairs x ys

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = let mkp = (,) x
               in Prelude.map mkp xs ++ pairs xs
