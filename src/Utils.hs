{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}

module Utils where

import qualified Data.Map.Lazy as M
import qualified Data.List as L
import Data.Bits (Bits(shiftL, (.|.)))

{-# INLINABLE maxBy #-}
maxBy :: (a -> a -> Ordering) -> a -> a -> a
maxBy cmp x y
 = if res == LT then y else x
   where
     res = cmp x y

calcMagicConstant :: [Integer] -> Integer -> Integer
calcMagicConstant xs bitsInWord = c
  where
    one = 1 :: Integer
    bitsInW = bitsInWord - 1
    c = L.foldl' (\acc x -> acc .|. shiftToPos x) (0 :: Integer) xs
    shiftToPos n = one `shiftL` fromIntegral (bitsInW - n)

{-# INLINABLE calcRevMap #-}
calcRevMap :: Ord b => M.Map a b -> M.Map b [a]
calcRevMap = M.foldrWithKey' (\n label m -> M.insertWith (++) label [n] m) M.empty

isDense :: [Integer] -> Bool
isDense [] = True
isDense ns = len == span
  where
    firstNum = head ns
    (len, lastNum) = go ns 1
    span = fromIntegral (lastNum - firstNum) + 1

    go :: [Integer] -> Int -> (Int, Integer)
    go [n] !len = (len, n)
    go (_ : ns) !len = go ns (len + 1)
    go [] _ = error "The improssible happened!"

isDenseEnough :: Integer -> [Integer] -> Bool
isDenseEnough _gap [] = True
isDenseEnough gap (cur : ns)
  = go cur ns
  where
    go prev (cur : ns) = cur - prev <= gap && go cur ns
    go _prev [] = True

{-# INLINABLE ind #-}
ind :: Bool -> Int 
ind b = if b then 1 else 0
