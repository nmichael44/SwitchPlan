{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}

module Switch where

import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.List as L
import qualified Numeric as N
import qualified Data.Char as C
import qualified Data.Maybe as Maybe

import Data.List(foldl')
import Data.Bits

import Debug.Trace

someFunc :: IO ()
someFunc = putStrLn "someFunc"

data SwitchTargets =
    SwitchTargets
        Bool                       -- Signed values
        (Integer, Integer)         -- Range
        (Maybe Label)              -- Default value
        (M.Map Integer Label)      -- The branches
        (M.Map Label [Integer])    -- The reverse of the above Map
        [(Integer, Label)]         -- Flattened branches
    deriving (Show, Eq)

mkSwitchTargets :: Bool -> (Integer, Integer) -> Maybe Label -> M.Map Integer Label -> SwitchTargets
mkSwitchTargets signed range defLabel intToLabel
  = SwitchTargets signed range defLabel intToLabel (calcRevMap intToLabel) (M.toList intToLabel)

newtype Label = L Integer
  deriving (Eq, Ord)

instance Show Label where
  show :: Label -> String 
  show (L n) = "L" ++ show n

bytesInWordForPlatform :: Int
bytesInWordForPlatform = 8

bitsInWordForPlatform = bytesInWordForPlatform * 8

zeros :: String
zeros = replicate bitsInWordForPlatform '0'

instance Show BitTestInfo where
  show :: BitTestInfo -> String 
  show BitTestInfo { offset, magicConstant, bitTestFailedPlan }
    = "BitTestInfo { offset = "
        ++ show offset
        ++ ", magicConst = "
        ++ reverse (take bitsInWordForPlatform (reverse (zeros ++ N.showIntAtBase 2 C.intToDigit magicConstant "")))
        ++ (", bitTestFailedPlan = " ++ show bitTestFailedPlan
        ++ " }")

data BitTestInfo
    = BitTestInfo { offset :: Maybe Integer, magicConstant :: Integer, bitTestFailedPlan :: SwitchPlan }

-- A BitTestOptInfo describes one partilar IfBitTest.
-- See Note [Compiling BitTest case statements] for more details.
data BitTestOptInfo
    = BTOI {
        bitTestInfo :: BitTestInfo
      , bitTestSucceededPlan :: SwitchPlan }
  deriving Show

data SwitchPlan
    = Unconditionally Label
    | IfEqual Integer Label SwitchPlan
    | IfLT Bool Integer SwitchPlan SwitchPlan
    | IfLE Bool Integer SwitchPlan SwitchPlan
    | BitTest BitTestOptInfo
    | JumpTable SwitchTargets
  deriving Show

newtype Platform = Platform Int

calcMagicConstant :: [Integer] -> Integer -> Integer
calcMagicConstant xs bitsInWord = c
  where
    one = 1 :: Integer
    bitsInW = bitsInWord - 1
    c = foldl' (\acc x -> acc .|. shiftToPos x) (0 :: Integer) xs
    shiftToPos n = one `shiftL` fromIntegral (bitsInW - n)

calcRevMap :: M.Map Integer Label -> M.Map Label [Integer]
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

isAlmostDense :: Integer -> [Integer] -> Bool
isAlmostDense _gap [] = True
isAlmostDense gap (cur : ns)
  = go cur ns
  where
    go prev (cur : ns) = cur - prev <= gap && go cur ns
    go _prev [] = True

ind :: Bool -> Int 
ind b = if b then 1 else 0

platformWordSizeInBytes :: Platform -> Int
platformWordSizeInBytes (Platform n) = n

createPlan :: SwitchTargets -> Platform -> SwitchPlan
createPlan st@(SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts intLabelList) platform
  = if | [(n, label)] <- intLabelList
         , Just defLabel <- defLabelOpt -- todo: have a look at this again later.  Does it ever happen?
         -> IfEqual n label (Unconditionally defLabel)

       | Just plan <- createTwoValBitTest st bitsInWord
         -> plan

       | Just plan <- createThreeValPlanNoDefault st platform
         -> plan

       | Just plan <- createGeneralBitTest st platform
         -> plan

       | Just plan <- createJumpTable st
         -> plan

       | otherwise ->
           -- split the interval in two in an intelligent way
           -- and recurce twice to finish the job
           -- returning something like if (x < expr) then plan1 else plan2
           undefined
  where
    bitsInWord = 8 * fromIntegral (platformWordSizeInBytes platform)

createTwoValBitTest :: SwitchTargets -> Integer -> Maybe SwitchPlan
createTwoValBitTest st@(SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts intLabelList) bitsInWord
  = if numLabels /= 2
    then Nothing
    else
      let
        [label1, label2] = S.toList labelSet
      in
        case defLabelOpt of 
          Just defLabel -> createBitTestForTwoLabelsWithDefault st (if label1 == defLabel then label2 else label1) bitsInWord
          Nothing -> createBitTestForTwoLabelsNoDefault st label1 label2 bitsInWord
  where
    -- We have to do this because one of the integer labels could be the same as the default label
    -- Thus we build a set to remove possible duplicates.
    labelSet = let s = M.keysSet labelToInts in maybe s (`S.insert` s) defLabelOpt
    numLabels = S.size labelSet

-- Function creates a plan 
createBitTestForTwoLabelsNoDefault :: SwitchTargets -> Label -> Label -> Integer -> Maybe SwitchPlan
createBitTestForTwoLabelsNoDefault
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts intLabelList)
  label1
  label2
  bitsInWord
  = let
      label1Ints = case M.lookup label1 labelToInts of { Just ns -> ns; Nothing -> error "The improssible happened" }
      label2Ints = case M.lookup label2 labelToInts of { Just ns -> ns; Nothing -> error "The improssible happened" }

      region1IsDense = isDense label1Ints
      region2IsDense = isDense label2Ints

      region1Lb = head label1Ints
      region1Ub = last label1Ints
      region2Lb = head label2Ints
      region2Ub = last label2Ints

      region1Count = length label1Ints
      region2Count = length label2Ints
      
      span1 = region1Ub - region1Lb + 1
      span2 = region2Ub - region2Lb + 1
      totalSpan = ub - lb + 1

      doLeftCheckRegion1 = lb < region1Lb
      doRightCheckRegion1 = ub > region1Ub

      doLeftCheckRegion2 = lb < region2Lb
      doRightCheckRegion2 = ub > region2Ub

      numChecksForRegion1 = ind doLeftCheckRegion1 + ind doRightCheckRegion1
      numChecksForRegion2 = ind doLeftCheckRegion2 + ind doRightCheckRegion2

      lab1Plan = Unconditionally label1
      lab2Plan = Unconditionally label2
      lab1PlanOpt = Just lab1Plan
      lab2PlanOpt = Just lab2Plan
    in
      if | region1Count == 1 -> Just $ IfEqual region1Lb label1 lab2Plan

         | region2Count == 1 -> Just $ IfEqual region2Lb label2 lab1Plan

         | region1IsDense && numChecksForRegion1 < 2 ->
             Just $ cbp signed doLeftCheckRegion1 lab2PlanOpt doRightCheckRegion1 lab2PlanOpt lab1Plan region1Lb region1Ub

         | region2IsDense && numChecksForRegion2 < 2 ->
             Just $ cbp signed doLeftCheckRegion2 lab1PlanOpt doRightCheckRegion2 lab1PlanOpt lab2Plan region2Lb region2Ub

         | totalSpan <= bitsInWord -> Just $ createBitTestPlan label1 label1Ints lb ub label2 bitsInWord

         | region1IsDense ->
             Just $ cbp signed doLeftCheckRegion1 lab2PlanOpt doRightCheckRegion1 lab2PlanOpt lab1Plan region1Lb region1Ub

         | region2IsDense ->
             Just $ cbp signed doLeftCheckRegion2 lab1PlanOpt doRightCheckRegion2 lab1PlanOpt lab2Plan region2Lb region2Ub

         | region1Count == 2 -> Just $ createEqPlan label1Ints label1 label2

         | region2Count == 2 -> Just $ createEqPlan label2Ints label2 label1

         | otherwise ->
           let
             region1Score = ind (span1 > bitsInWord) * 10 + numChecksForRegion1
             region2Score = ind (span2 > bitsInWord) * 10 + numChecksForRegion2

             minScore = min region1Score region2Score
           in
             if minScore >= 10
             then
               if | region1Count == 3 -> Just $ createEqPlan label1Ints label1 label2
                  | region2Count == 3 -> Just $ createEqPlan label2Ints label2 label1
                  | otherwise -> Nothing
             else
               Just $
               if region1Score == minScore
               then cbp signed doLeftCheckRegion1 lab2PlanOpt doRightCheckRegion1 lab2PlanOpt
                        (createBitTestPlan label1 label1Ints region1Lb region1Ub label2 bitsInWord)
                        region1Lb region1Ub
               else cbp signed doLeftCheckRegion2 lab1PlanOpt doRightCheckRegion2 lab1PlanOpt
                        (createBitTestPlan label2 label2Ints region2Lb region2Ub label1 bitsInWord)
                        region2Lb region2Ub

maxSizeOfSpanForDefaultExpand :: Int
maxSizeOfSpanForDefaultExpand = 256

-- defLabel is one of { label1, label2 }
createBitTestForTwoLabelsWithDefault :: SwitchTargets -> Label -> Integer -> Maybe SwitchPlan
createBitTestForTwoLabelsWithDefault
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts intLabelList)
    label
    bitsInWord
  = let
      defLabel = Maybe.fromJust defLabelOpt
      totalSpan = fromIntegral (ub - lb + 1)

      intsGoingToDefaultLabel = Maybe.fromMaybe [] (M.lookup defLabel labelToInts)
      intToLabel' = foldl' (flip M.delete) intToLabel intsGoingToDefaultLabel
      labelToInts' = M.delete defLabel labelToInts
    in
      if totalSpan <= maxSizeOfSpanForDefaultExpand
      then
        let
          numLabelForDefault = [(i, defLabel) | i <- [lb..ub], not (i `M.member` intToLabel')]

          intToLabel'' = foldl' (\m (i, l) -> M.insert i l m) intToLabel' numLabelForDefault
          labelToInts'' = M.insert defLabel (fst <$> numLabelForDefault) labelToInts'
                        
          st' = SwitchTargets signed range Nothing intToLabel'' labelToInts'' (M.toList intToLabel'')
        in
           createBitTestForTwoLabelsNoDefault st' label defLabel bitsInWord
      else
        let
          labelInts = case M.lookup label labelToInts' of { Just ns -> ns; Nothing -> error "The improssible happened" }
          regionCount = length labelInts
          regionIsDense = isDense labelInts

          regionLb = head labelInts
          regionUb = last labelInts

          doLeftCheckRegion = lb < regionLb
          doRightCheckRegion = ub > regionUb

          numChecksForRegion = ind doLeftCheckRegion + ind doRightCheckRegion

          labPlan = Unconditionally label
          defPlan = Unconditionally defLabel
          labPlanOpt = Just labPlan
          defPlanOpt = Just defPlan

          spanOfRegion = regionUb - regionLb + 1
        in
          if | regionCount == 1 -> Just $ IfEqual (head labelInts) label $ Unconditionally defLabel
             | regionIsDense ->
                 Just $ cbp signed doLeftCheckRegion defPlanOpt doRightCheckRegion defPlanOpt labPlan regionLb regionUb
             | regionCount == 2 -> Just $ createEqPlan labelInts label defLabel
             | spanOfRegion <= bitsInWord ->
                 Just $ cbp signed doLeftCheckRegion defPlanOpt doRightCheckRegion defPlanOpt
                            (createBitTestPlan label labelInts regionLb regionUb defLabel bitsInWord)
                            regionLb regionUb
             | regionCount == 3 -> Just $ createEqPlan labelInts label defLabel
             | otherwise -> Nothing

newtype T = T (Maybe (Label, Integer, Bool, Bool))

instance Eq T where
  (T Nothing) == (T Nothing) = True 
  (T (Just (_, _, eqLb, eqUb))) == (T (Just (_, _, eqLb', eqUb'))) = eqLb == eqLb' && eqUb == eqUb'
  _ == _ = False
 
instance Ord T where
  compare (T Nothing) (T Nothing) = EQ 
  compare (T Nothing) (T (Just _)) = LT
  compare (T (Just _)) (T Nothing) = GT 
  compare (T (Just (lab, n, eqLb, eqUb))) (T (Just (lab', n', eqLb', eqUb')))
    = case compare eqLb eqLb' of
        EQ -> compare eqUb eqUb'
        x -> x

createThreeValPlanNoDefault :: SwitchTargets -> Platform -> Maybe SwitchPlan
createThreeValPlanNoDefault
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts intLabelList)
  platform
  = if Maybe.isJust defLabelOpt || M.size labelToInts /= 3
    then trace (show (M.size labelToInts)) Nothing
    else
      let
        [(lab1, label1Ints), (lab2, label2Ints), (lab3, label3Ints)] = M.toList labelToInts
        classLab1 = classifyCandidate lab1 label1Ints
        classLab2 = classifyCandidate lab2 label2Ints
        classLab3 = classifyCandidate lab3 label3Ints

        candidate = max classLab1 (max classLab2 classLab3)
      in
        case candidate of
          (T (Just (lab, n, eqLb, eqUb))) -> Just $ createFullPlan lab n eqLb eqUb
          (T Nothing) -> Nothing
  where
    classifyCandidate lab [n] = T $ Just (lab, n, n == lb, n == ub)
    classifyCandidate _ _ = T Nothing

    createFullPlan :: Label -> Integer -> Bool -> Bool -> SwitchPlan
    createFullPlan labelToRemove n eqLb eqUb
      = let
          intToLabel' = M.delete n intToLabel
          labelToInts' = M.delete labelToRemove labelToInts
          intLabelList' = L.delete (n, labelToRemove) intLabelList
          range' = if | eqLb -> (lb + 1, ub)
                      | eqUb -> (lb, ub -1)
                      | otherwise -> range

          st' = SwitchTargets signed range' defLabelOpt intToLabel' labelToInts' intLabelList'
        in
          IfEqual n labelToRemove $ createPlan st' platform

createGeneralBitTest :: SwitchTargets -> Platform -> Maybe SwitchPlan
createGeneralBitTest
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts intLabelList)
  bitsInWord
 = undefined

createJumpTable :: SwitchTargets -> Maybe SwitchPlan
createJumpTable (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts intLabelList)
  = undefined

cbp :: Bool -> Bool -> Maybe SwitchPlan -> Bool -> Maybe SwitchPlan -> SwitchPlan 
       -> Integer -> Integer -> SwitchPlan
cbp signed doLeftCheck leftPlan doRightCheck rightPlan
  = createBracketPlan
      signed
      (if doLeftCheck then leftPlan else Nothing)
      (if doRightCheck then rightPlan else Nothing)

createEqPlan :: [Integer] -> Label -> Label -> SwitchPlan
createEqPlan labelInts lab1 lab2
  = foldl' (\plan n -> IfEqual n lab1 plan) (Unconditionally lab2) labelInts

createBitTestPlan :: Label -> [Integer] -> Integer -> Integer -> Label -> Integer -> SwitchPlan
createBitTestPlan bitTestLabel intsOfLabel regionLb regionUb otherLabel bitsInWord
  = let
      canSkipOffset = regionLb >= 0 && regionUb < bitsInWord
      (offset, constants) = if canSkipOffset then (Nothing, intsOfLabel)
                            else (Just regionLb, (\n -> n - regionLb) <$> intsOfLabel)
      magicConstant = calcMagicConstant constants bitsInWord
      otherLabelPlan = Unconditionally otherLabel
      bitTestInfo = BitTestInfo { offset = offset
                                , magicConstant = magicConstant
                                , bitTestFailedPlan = otherLabelPlan }
    in
      BitTest (BTOI { bitTestInfo = bitTestInfo
                    , bitTestSucceededPlan = Unconditionally bitTestLabel})

createBracketPlan :: Bool -> Maybe SwitchPlan -> Maybe SwitchPlan -> SwitchPlan
                     -> Integer -> Integer -> SwitchPlan
createBracketPlan signed leftBracketPlanOpt rightBracketPlanOpt bitTestPlan lb ub
  = case (leftBracketPlanOpt, rightBracketPlanOpt) of

      (Just leftPlan, Just rightPlan)
        -> IfLT signed lb leftPlan (IfLE signed ub bitTestPlan rightPlan)

      (Just leftPlan, Nothing)
        -> IfLT signed lb leftPlan bitTestPlan

      (Nothing, Just rightPlan)
        -> IfLE signed ub bitTestPlan rightPlan

      (Nothing, Nothing) -> bitTestPlan

lab1 :: Label
lab1 = L 1
lab2 :: Label
lab2 = L 2
lab3 :: Label
lab3 = L 3

st1 :: SwitchTargets
st1 = mkSwitchTargets True (1,3) (Just lab3)
       (M.fromList [(1, lab1), (2, lab2)])
pl = Platform 64

{-
st2 :: SwitchTargets
st2 = mkSwitchTargets True (0, 7) Nothing
       (M.fromList [(0, lab1), (1, lab1), (2, lab2), (3, lab2),
                    (4, lab1), (5, lab1), (6, lab1), (7, lab1)])

st3 :: SwitchTargets
st3 = mkSwitchTargets True (-1, 6) Nothing
       (M.fromList [(-1, lab1), (0, lab1), (1, lab2), (2, lab2),
                    (3, lab1), (4, lab1), (5, lab1), (6, lab1)])

st4 :: SwitchTargets
st4 = mkSwitchTargets True (1,5) Nothing
       (M.fromList [(1, lab2), (2, lab1), (3, lab1), (4, lab2), (5, lab1)])

st5 :: SwitchTargets
st5 = mkSwitchTargets True (0,9) Nothing
       (M.fromList [(0, lab2), (1, lab1), (2, lab1), (3, lab1), (4, lab2), (5, lab1),
                    (6, lab1), (7, lab1), (8, lab1), (9, lab1)])
-}
