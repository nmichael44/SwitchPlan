{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}

module Utils (
  maxBy
  , minBy
  , calcMagicConstant
  , calcRevMap
  , isDense
  , isDenseEnough
  , ind
  , findRegionSeparators
  , findMiddleOfList) where

import qualified Data.Map.Lazy as M
import qualified Data.List as L
import qualified Data.Bits as Bits

{-# INLINABLE maxBy #-}
maxBy :: (a -> a -> Ordering) -> a -> a -> a
maxBy cmp x y = if cmp x y == LT then y else x

{-# INLINABLE minBy #-}
minBy :: (a -> a -> Ordering) -> a -> a -> a
minBy cmp x y = if cmp x y == GT then y else x

{-# INLINABLE calcMagicConstant #-}
calcMagicConstant :: [Integer] -> Integer -> Integer
calcMagicConstant xs bitsInWord = c
  where
    bitsInW = bitsInWord - 1
    c = L.foldl' (\acc x -> (Bits..|.) acc (shiftToPos x)) (0 :: Integer) xs
    shiftToPos n = Bits.shiftL (1 :: Integer) (fromIntegral (bitsInW - n))

{-# INLINABLE calcRevMap #-}
calcRevMap :: Ord b => M.Map a b -> M.Map b [a]
calcRevMap = M.foldrWithKey' (\n label m -> M.insertWith (++) label [n] m) M.empty

{-# INLINABLE isDense #-}
isDense :: [Integer] -> Bool
isDense [] = True
isDense ys = lenList == regionSpan
  where
    firstNum = head ys
    (lenList, lastNum) = go ys 1
    regionSpan = fromIntegral (lastNum - firstNum) + 1

    go :: [Integer] -> Int -> (Int, Integer)
    go [n] !len = (len, n)
    go (_ : ns) !len = go ns (len + 1)
    go [] _ = error "The impossible happened!"

{-# INLINABLE isDenseEnough #-}
isDenseEnough :: Integer -> [Integer] -> Bool
isDenseEnough _gap [] = True
isDenseEnough gap (current : ns) = go current ns
  where
    go prev (cur : xs) = cur - prev <= gap && go cur xs
    go _prev [] = True

{-# INLINABLE ind #-}
ind :: Bool -> Int 
ind b = if b then 1 else 0

-- Returns a list of all the start elements of the various regions of the list
-- e.g. findRegionSeparators 2 [1,2, 4, 6,7,8, 10,11]   ==>  [1, 4, 6, 10]
{-# INLINABLE findRegionSeparators #-}
findRegionSeparators :: (Num a, Ord a) => a -> [a] -> [a]
findRegionSeparators gap ns@(start : _)  = start : [y | (x, y) <- zip ns (tail ns), y - x >= gap]
findRegionSeparators _gap [] = error "Must never be called on an empty list."

-- Finds the middle element of a list.
-- If the list has even size then it returns the element on the right of middle.
-- Throws an exception on an empty list.
{-# INLINABLE findMiddleOfList #-}
findMiddleOfList :: [a] -> a
findMiddleOfList ns
  = go ns ns
  where
    go (x : _) [] = x
    go (x : _) [_] = x
    go (_ : xs) (_ : _ : ys) = go xs ys
    go [] _ = error "Must never be called on an empty list."
