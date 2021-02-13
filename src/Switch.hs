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
import qualified Utils as U

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
    deriving (Show, Eq)

mkSwitchTargets :: Bool -> (Integer, Integer) -> Maybe Label -> M.Map Integer Label -> SwitchTargets
mkSwitchTargets signed range defLabel intToLabel
  = SwitchTargets signed range defLabel intToLabel (U.calcRevMap intToLabel)

newtype Label = L Integer
  deriving (Eq, Ord)

instance Show Label where
  show :: Label -> String
  show (L n) = "L" ++ show n

bytesInWordForPlatform :: Int
bytesInWordForPlatform = 8

bitsInWordForPlatform :: Int
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

data SwitchPlan
    = Unconditionally Label
    | IfEqual Integer Label SwitchPlan
    | IfLT Bool Integer SwitchPlan SwitchPlan
    | IfLE Bool Integer SwitchPlan SwitchPlan
    | BitTest BitTestInfo SwitchPlan
    | JumpTable SwitchTargets
  deriving Show

newtype Platform = Platform Int

platformWordSizeInBytes :: Platform -> Int
platformWordSizeInBytes (Platform n) = n

createPlan :: SwitchTargets -> Platform -> SwitchPlan
createPlan st@(SwitchTargets signed _range _defLabelOpt _intToLabel _labelToInts) platform
  =
{-     if | [(n, label)] <- intLabelList
         , Just defLabel <- defLabelOpt -- todo: have a look at this again later.  Does it ever happen?
         -> IfEqual n label (Unconditionally defLabel)
-}
    if | Just plan <- createTwoValBitTest st platform
          -> plan

       | Just plan <- createThreeValPlanNoDefault st platform
         -> plan

       | Just plan <- createGeneralBitTest st platform
         -> plan

       | Just plan <- createJumpTable st
         -> plan

       | otherwise ->
         let
           (stLeft, n, stRight) = splitInterval st
         in
           IfLT signed n (createPlan stLeft platform) (createPlan stRight platform)

createTwoValBitTest :: SwitchTargets -> Platform -> Maybe SwitchPlan
createTwoValBitTest st@(SwitchTargets _signed _range defLabelOpt _intToLabel labelToInts) platform
  = if numLabels /= 2
    then Nothing
    else
      let
        -- Can never fail but let's silence the ghc warning.
        (label1, label2) = case S.toList labelSet of { [lab1, lab2] -> (lab1, lab2); _ -> error "The improssible happened" }
      in
        case defLabelOpt of 
          Just defLabel -> createBitTestForTwoLabelsWithDefault st (if label1 == defLabel then label2 else label1) bitsInWord
          Nothing -> createBitTestForTwoLabelsNoDefault st label1 label2 bitsInWord
  where
    -- We have to do this because one of the integer labels could be the same as the default label
    -- Thus we build a set to remove possible duplicates.
    labelSet = let s = M.keysSet labelToInts in maybe s (`S.insert` s) defLabelOpt
    numLabels = S.size labelSet
    bitsInWord = 8 * fromIntegral (platformWordSizeInBytes platform)

-- Function creates a plan 
createBitTestForTwoLabelsNoDefault :: SwitchTargets -> Label -> Label -> Integer -> Maybe SwitchPlan
createBitTestForTwoLabelsNoDefault
  (SwitchTargets signed (lb, ub) _defLabelOpt _intToLabel labelToInts)
  label1
  label2
  bitsInWord
  = let
      label1Ints = case M.lookup label1 labelToInts of { Just ns -> ns; Nothing -> error "The improssible happened" }
      label2Ints = case M.lookup label2 labelToInts of { Just ns -> ns; Nothing -> error "The improssible happened" }

      region1IsDense = U.isDense label1Ints
      region2IsDense = U.isDense label2Ints

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

      numChecksForRegion1 = U.ind doLeftCheckRegion1 + U.ind doRightCheckRegion1
      numChecksForRegion2 = U.ind doLeftCheckRegion2 + U.ind doRightCheckRegion2

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
             region1Score = U.ind (span1 > bitsInWord) * 10 + numChecksForRegion1
             region2Score = U.ind (span2 > bitsInWord) * 10 + numChecksForRegion2

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

maxExpandSizeForDefault :: Integer
maxExpandSizeForDefault = 128

createBitTestForTwoLabelsWithDefault :: SwitchTargets -> Label -> Integer -> Maybe SwitchPlan
createBitTestForTwoLabelsWithDefault
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts)
    label
    bitsInWord
  = let
      defLabel = Maybe.fromJust defLabelOpt
      totalSpan = ub - lb + 1

      intsGoingToDefaultLabel = Maybe.fromMaybe [] (M.lookup defLabel labelToInts)
      intToLabel' = L.foldl' (flip M.delete) intToLabel intsGoingToDefaultLabel
      labelToInts' = M.delete defLabel labelToInts
    in
      if totalSpan <= maxExpandSizeForDefault
      then
        let
          numLabelForDefault = [(i, defLabel) | i <- [lb..ub], not (i `M.member` intToLabel')]

          intToLabel'' = L.foldl' (\m (i, l) -> M.insert i l m) intToLabel' numLabelForDefault
          labelToInts'' = M.insert defLabel (fst <$> numLabelForDefault) labelToInts'
                        
          st' = SwitchTargets signed range Nothing intToLabel'' labelToInts''
        in
           createBitTestForTwoLabelsNoDefault st' label defLabel bitsInWord
      else
        let
          labelInts = case M.lookup label labelToInts' of { Just ns -> ns; Nothing -> error "The impossible happened!" }
          regionCount = length labelInts
          regionIsDense = U.isDense labelInts

          regionLb = head labelInts
          regionUb = last labelInts

          doLeftCheckRegion = lb < regionLb
          doRightCheckRegion = ub > regionUb

          labPlan = Unconditionally label
          defPlan = Unconditionally defLabel
          defPlanOpt = Just defPlan

          spanOfRegion = regionUb - regionLb + 1
        in
          if | regionCount == 1 -> Just $ IfEqual (head labelInts) label defPlan
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

compT :: T -> T -> Ordering
compT (T Nothing) (T Nothing) = EQ 
compT (T Nothing) (T (Just _)) = LT
compT (T (Just _)) (T Nothing) = GT 
compT (T (Just (_, _, eqLb, eqUb))) (T (Just (_, _, eqLb', eqUb')))
  = case compare eqLb eqLb' of
      EQ -> compare eqUb eqUb'
      x -> x

createThreeValPlanNoDefault :: SwitchTargets -> Platform -> Maybe SwitchPlan
createThreeValPlanNoDefault
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts)
  platform
  = if Maybe.isJust defLabelOpt || M.size labelToInts /= 3
    then Nothing
    else
      let                                                            -- Can never fail but let's silence the ghc warning.
        ((lab1, label1Ints), (lab2, label2Ints), (lab3, label3Ints)) = case M.toList labelToInts of { [p0, p1, p2] -> (p0, p1, p2); _ -> error "The impossible happened!" }
        classLab1 = classifyCandidate lab1 label1Ints
        classLab2 = classifyCandidate lab2 label2Ints
        classLab3 = classifyCandidate lab3 label3Ints

        candidate = U.maxBy compT classLab1 (U.maxBy compT classLab2 classLab3)
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
          range' = if | eqLb -> (lb + 1, ub)
                      | eqUb -> (lb, ub -1)
                      | otherwise -> range

          st' = SwitchTargets signed range' defLabelOpt intToLabel' labelToInts'
        in
          IfEqual n labelToRemove $ createPlan st' platform

createGeneralBitTest :: SwitchTargets -> Platform -> Maybe SwitchPlan
createGeneralBitTest
  (SwitchTargets _signed _range@(_lb, _ub) _defLabelOpt _intToLabel _labelToInts)
  _bitsInWord
 = Nothing

maxJumpTableGapSize :: Integer
maxJumpTableGapSize = 6

minJumpTableSize :: Int
minJumpTableSize = 5

minJumpTableOffset :: Integer
minJumpTableOffset = 2

createJumpTable :: SwitchTargets -> Maybe SwitchPlan
createJumpTable st@(SwitchTargets _signed (lb, ub) defLabelOpt intToLabel _labelToInts)
  = case defLabelOpt of
      Just _ ->
        let
          spanOfFullRegion = ub - lb + 1
        in
          if spanOfFullRegion <= maxExpandSizeForDefault
          then createJumpTableAux (expandRegion st lb ub) True
          else
            let
              (regionLb, _) = M.findMin intToLabel
              (regionUb, _) = M.findMax intToLabel
              spanOfCases = regionUb - regionLb + 1
            in
              if spanOfCases <= maxExpandSizeForDefault
              then createJumpTableAux (expandRegion st regionLb regionUb) True
              else createJumpTableAux st False
      Nothing -> createJumpTableAux st True

createJumpTableAux :: SwitchTargets -> Bool -> Maybe SwitchPlan
createJumpTableAux st@(SwitchTargets _signed _range _defLabelOpt intToLabel _labelToInts) hasBeenExpanded
  = let
      numCases = M.size intToLabel
    in
      if | numCases < minJumpTableSize -> Nothing
          | not hasBeenExpanded && not (U.isDenseEnough maxJumpTableGapSize $ M.keys intToLabel) -> Nothing
          | otherwise -> Just $ JumpTable st

splitInterval :: SwitchTargets -> (SwitchTargets, Integer, SwitchTargets)
splitInterval (SwitchTargets signed (lb, ub) defLabelOpt intToLabel _labelToInts)
  = let
      caseInts = M.keys intToLabel
      regionSeparators = U.findRegionSeparators maxJumpTableGapSize caseInts
      midSeparator = U.findMiddleOfList regionSeparators

      (intToLabelLeft, intToLabelRight) = U.splitMapInTwo midSeparator intToLabel

      stLeft = mkSwitchTargets signed (lb, midSeparator - 1) defLabelOpt intToLabelLeft
      stRight = mkSwitchTargets signed (midSeparator, ub) defLabelOpt intToLabelRight
    in
      (stLeft, midSeparator, stRight)

expandRegion :: SwitchTargets -> Integer -> Integer -> SwitchTargets
expandRegion (SwitchTargets signed range@(lb, ub) defLabelOpt@(Just defLabel) intToLabel labelToInts) regLb regUb
  = let
      existingIntsGointToDefault = Maybe.fromMaybe [] $ M.lookup defLabel labelToInts
      intToLabel' = L.foldl' (flip M.delete) intToLabel existingIntsGointToDefault
      labelToInts' = M.delete defLabel labelToInts

      numCasesForDefault = [(i, defLabel) | i <- [regLb..regUb], not (i `M.member` intToLabel')]

      intToLabel'' = L.foldl' (\m (i, l) -> M.insert i l m) intToLabel' numCasesForDefault
      labelToInts'' = M.insert defLabel (fst <$> numCasesForDefault) labelToInts'

      defl = if regLb == lb && regUb == ub then Nothing else defLabelOpt
    in
      SwitchTargets signed range defl intToLabel'' labelToInts''

expandRegion (SwitchTargets _ _ Nothing _ _) _ _ = error "The impossible happened!"

cbp :: Bool -> Bool -> Maybe SwitchPlan -> Bool -> Maybe SwitchPlan -> SwitchPlan 
       -> Integer -> Integer -> SwitchPlan
cbp signed doLeftCheck leftPlan doRightCheck rightPlan
  = createBracketPlan
      signed
      (if doLeftCheck then leftPlan else Nothing)
      (if doRightCheck then rightPlan else Nothing)

createEqPlan :: [Integer] -> Label -> Label -> SwitchPlan
createEqPlan labelInts lab1 lab2
  = L.foldl' (\plan n -> IfEqual n lab1 plan) (Unconditionally lab2) labelInts

createBitTestPlan :: Label -> [Integer] -> Integer -> Integer -> Label -> Integer -> SwitchPlan
createBitTestPlan bitTestLabel intsOfLabel regionLb regionUb otherLabel bitsInWord
  = let
      canSkipOffset = regionLb >= 0 && regionUb < bitsInWord
      (offset, constants) = if canSkipOffset then (Nothing, intsOfLabel)
                            else (Just regionLb, (\n -> n - regionLb) <$> intsOfLabel)
      magicConstant = U.calcMagicConstant constants bitsInWord
      otherLabelPlan = Unconditionally otherLabel
      bitTestInfo = BitTestInfo { offset = offset
                                , magicConstant = magicConstant
                                , bitTestFailedPlan = otherLabelPlan }
    in
      BitTest bitTestInfo $ Unconditionally bitTestLabel

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

l1 :: Label
l1 = L 1
l2 :: Label
l2 = L 2
l3 :: Label
l3 = L 3

st1 :: SwitchTargets
st1 = mkSwitchTargets True (1,10) (Just l3)
       (M.fromList [(3, l2), (6, l1), (7, l1)])

pl :: Platform
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
