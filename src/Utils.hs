{-# LANGUAGE MultiWayIf #-}
module Utils where

maxBy :: (a -> a -> Ordering) -> a -> a -> a
maxBy cmp x y
 = if res == LT then y else x
   where
     res = cmp x y
