{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE TupleSections #-}

module SwitchUtils (
  maxBy
  , minBy
  , calcMagicConstant
  , calcMagicConstant2
  , calcRevMap
  , isDense
  , isDenseEnough
  , ind
  , findRegionSeparators
  , findMiddleOfList
  , splitMap
  , LocationOfElement(..)
  , buildMap
  , convIntegerToBinary
  , findPairWithMaxNumElems
  , firstSuccess
  , computeRangeOfComplement
  , computeMapWithinRangeInclusive
  , eliminateKeyFromMaps
  , rangeSpan
  , revAndLen
  , impossible
--  , splitAtHoles
--  , restrictMap
--  , reassocTuples
--  , breakTooSmall
   ) where

import qualified Data.Map.Lazy as M
import qualified Data.List as L
import qualified Data.Bits as Bits
import qualified Data.Foldable as F
import qualified Data.Maybe as Maybe
import Data.Function (on)

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

bitPatternsForMC2 :: [Integer]
bitPatternsForMC2 = [0b01, 0b10, 0b11]

{-# INLINABLE calcMagicConstant2 #-}
calcMagicConstant2 :: [[Integer]] -> (Integer, [Integer])
calcMagicConstant2 xxs = (c, L.take cnt bitPatternsForMC2)
  where
    cnt = length xxs
    numWithPattern = concatMap (\(xs, pat) -> map (\n -> (fromIntegral n, pat)) xs) $ zip xxs bitPatternsForMC2
    c = L.foldl' (\acc (n, pat) -> (Bits..|.) acc (Bits.shiftL pat (n + n))) 0 numWithPattern

{-# INLINABLE calcRevMap #-}
calcRevMap :: Ord b => M.Map a b -> M.Map b [a]
calcRevMap = M.foldrWithKey' (\n label m -> M.insertWith (++) label [n] m) M.empty

{-# INLINABLE isDense #-}
isDense :: [Integer] -> Bool
isDense [] = True
isDense (current : ys) = go current ys
  where
    go prev (cur : xs) = cur - prev == 1 && go cur xs
    go _prev [] = True

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

data LocationOfElement = LeftMap | RightMap

-- Splits a (Map k v) into two Maps (m0, m1) such that all keys of m0 are < k and all keys of m1 are >= k.
-- If k happens to be in the map then it will be found in m1.
{-# INLINABLE splitMap #-}
splitMap :: Ord k => k -> M.Map k v -> LocationOfElement -> (M.Map k v, M.Map k v)
splitMap k m loc
  = case M.splitLookup k m of
      (m0, Nothing, m1) -> (m0, m1)
      (m0, Just v, m1) ->
        case loc of
          LeftMap -> (M.insert k v m0, m1)
          RightMap -> (m0, M.insert k v m1)

{-# INLINABLE buildMap #-}
buildMap :: (Show k, Show v, Ord k) => [(k, v)] -> Either String (M.Map k v)
buildMap = go M.empty
  where
    go m [] = Right m
    go m ((k, v) : kvs)
      = if k `M.member` m
        then Left $ "Duplicate found: " ++ show (k, v)
        else go (M.insert k v m) kvs

{-# INLINABLE convIntegerToBinary #-}
convIntegerToBinary :: Int -> Integer -> String
convIntegerToBinary numBits n
  = go numBits 1 ""
  where
    go :: Int -> Integer -> String -> String
    go 0 _ !acc = acc
    go cnt !m !acc = go (cnt - 1) (m `Bits.shiftL` 1) $ (if n Bits..&. m /= 0 then '1' else '0') : acc

{-# INLINABLE findPairWithMaxNumElems #-}
findPairWithMaxNumElems :: M.Map b [a] -> (b, [a])
findPairWithMaxNumElems m =
  F.maximumBy (compare `on` (length . snd)) (M.toList m)

{-# INLINABLE firstSuccess #-}
firstSuccess :: [Maybe a] -> Maybe a
firstSuccess = L.foldr (\opt res -> case opt of { Just _ -> opt; Nothing -> res }) Nothing

{-# INLINABLE computeRangeOfComplement #-}
computeRangeOfComplement :: (Num k, Ord k) => (k, k) -> M.Map k a -> (k, k)
computeRangeOfComplement (lb, ub) m
  = (leftStart, rightStart)
  where
    (mn, _) = M.findMin m
    (mx, _) = M.findMax m

    leftStart = if mn /= lb then lb else goFromLeft mn m
    rightStart = if mx /= ub then ub else goFromRight mx m

    goFromLeft, goFromRight :: (Num k, Ord k) => k -> M.Map k a -> k
    goFromLeft n mp
      = if n `M.member` mp then goFromLeft (n + 1) mp else n
    goFromRight n mp
      = if n `M.member` mp then goFromRight (n -1) mp else n

computeMapWithinRangeInclusive :: Ord k => (k, k) -> M.Map k v -> M.Map k v
computeMapWithinRangeInclusive (lb, ub) m
  = fst $ splitMap ub (snd $ splitMap lb m RightMap) LeftMap

{-# INLINABLE eliminateKeyFromMaps #-}
eliminateKeyFromMaps :: (Ord k1, Ord k2) => k2 -> M.Map k1 k2 -> M.Map k2 [k1] -> (M.Map k1 k2, M.Map k2 [k1])
eliminateKeyFromMaps k2 m0 m1
  = let
      keys = Maybe.fromMaybe [] (M.lookup k2 m1)
    in
      (L.foldl' (flip M.delete) m0 keys, M.delete k2 m1)

{-# INLINE rangeSpan #-}
rangeSpan :: Integral a => a -> a -> a
rangeSpan startN endN = endN - startN + 1

revAndLen :: [a] -> (Int, [a])
revAndLen xs
  = go xs 0 []
  where
    go :: [a] -> Int -> [a] -> (Int, [a])
    go [] len res = (len, res)
    go (y : ys) !len res = go ys (len + 1) (y : res)

impossible :: () -> as
impossible () = error "The impossible happened!"

{-
splitAtHoles :: Integer -> M.Map Integer a -> [M.Map Integer a]
splitAtHoles _        m | M.null m = []
splitAtHoles holeSize m = map (`restrictMap` m) nonHoles
  where
    holes = filter (\(l,h) -> h - l > holeSize) $ zip (M.keys m) (tail (M.keys m))
    nonHoles = reassocTuples lo holes hi

    (lo,_) = M.findMin m
    (hi,_) = M.findMax m

restrictMap :: (Integer,Integer) -> M.Map Integer b -> M.Map Integer b
restrictMap (lo,hi) m = mid
  where (_,   mid_hi) = M.split (lo-1) m
        (mid, _) =      M.split (hi+1) mid_hi

reassocTuples :: a -> [(a,a)] -> a -> [(a,a)]
reassocTuples initial [] last
    = [(initial,last)]
reassocTuples initial ((a,b):tuples) last
    = (initial,a) : reassocTuples b tuples last

minJumpTableSize :: Int
minJumpTableSize = 5

breakTooSmall :: M.Map Integer a -> [M.Map Integer a]
breakTooSmall m
  | M.size m > minJumpTableSize = [m]
  | otherwise                   = [M.singleton k v | (k,v) <- M.toList m]
-}