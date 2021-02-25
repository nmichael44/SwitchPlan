{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeApplications #-}

module Switch where

import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Maybe as Maybe
import qualified Data.Foldable as F
import qualified Utils as U

import Debug.Trace

data SwitchTargets =
    SwitchTargets
        Bool                       -- Signed values
        (Integer, Integer)         -- Range
        (Maybe Label)              -- Default value
        (M.Map Integer Label)      -- The branches
        (M.Map Label [Integer])    -- The reverse of the above Map
    deriving (Show, Eq)

getSigned :: SwitchTargets -> Bool
getSigned (SwitchTargets signed _ _ _ _) = signed

getDefLabel :: SwitchTargets -> Maybe Label
getDefLabel (SwitchTargets _ _ defLabelOpt _ _) = defLabelOpt

getLabelToInts :: SwitchTargets -> M.Map Label [Integer]
getLabelToInts (SwitchTargets _ _ _ _ labelToInts) = labelToInts

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

data BitTestInfo
  = BitTestInfo
      { offset :: Maybe Integer
      , magicConstant :: Integer
      , bitTestFailedPlan :: SwitchPlan }

data BitTestType2Info
  = BitTestType2Info
      { offset2 :: Maybe Integer
      , magicConstant2 :: Integer
      , bitTestFailedPlan2 :: SwitchPlan }

data SwitchPlan
  = Unconditionally Label
  | IfEqual Integer Label SwitchPlan
  | IfLT Bool Integer SwitchPlan SwitchPlan
  | IfLE Bool Integer SwitchPlan SwitchPlan
  | BitTest BitTestInfo SwitchPlan
  | BitTestType2 BitTestType2Info [(Integer, Label)]
  | JumpTable SwitchTargets
  deriving Show

instance Show BitTestInfo where
  show :: BitTestInfo -> String
  show BitTestInfo { offset, magicConstant, bitTestFailedPlan }
    = "BitTestInfo { offset = " ++ show offset
               ++ ", magicConst = " ++ U.convIntegerToBinary bitsInWordForPlatform magicConstant
               ++ ", bitTestFailedPlan = " ++ show bitTestFailedPlan ++ " }"

instance Show BitTestType2Info where
  show :: BitTestType2Info -> String
  show BitTestType2Info { offset2, magicConstant2, bitTestFailedPlan2 }
    = "BitTestType2Info { offset2 = " ++ show offset2
               ++ ", magicConst2 = " ++ U.convIntegerToBinary bitsInWordForPlatform magicConstant2
               ++ ", bitTestFailedPlan2 = " ++ show bitTestFailedPlan2 ++ " }"

newtype Platform = Platform Int

platformWordSizeInBytes :: Platform -> Int
platformWordSizeInBytes (Platform n) = n

switchTableEnabled :: Bool
switchTableEnabled = False

createPlan :: SwitchTargets -> Platform -> SwitchPlan
createPlan st platform
  = let
    -- We have to do this because one of the integer labels could be the same as the default label
    -- Thus we build a set to remove possible duplicates.
      labelSet = let s = M.keysSet (getLabelToInts st) in maybe s (`S.insert` s) (getDefLabel st)
      numLabels = S.size labelSet
      bitsInWord = 8 * fromIntegral (platformWordSizeInBytes platform)
    in
      trace ("NumLabels: " ++ show numLabels) $
      if | numLabels == 1, Just plan <- createOneValPlan labelSet
           -> trace "1!!!" plan
         | numLabels == 2, Just plan <- createTwoValPlan labelSet st bitsInWord
           -> trace "2!!!" plan
         | numLabels == 3, Just plan <- createThreeValPlan st bitsInWord platform
           -> trace "3!!!" plan
         | numLabels == 4, Just plan <- createFourValPlan st bitsInWord platform
           -> trace "4!!!" plan
         | switchTableEnabled, Just plan <- createJumpTable st
           -> trace "5!!!" plan
         | otherwise
           -> trace "6!!!" $ createSplitPlan (getSigned st) (splitInterval st) platform

createSplitPlan :: Bool -> (SwitchTargets, Integer, SwitchTargets) -> Platform -> SwitchPlan
createSplitPlan signed (stLeft, n, stRight) platform
  = IfLT signed n (createPlan stLeft platform) (createPlan stRight platform)

createOneValPlan :: S.Set Label -> Maybe SwitchPlan
createOneValPlan labelSet
  = let
      label = case S.toList labelSet of { [l] -> l; _ -> U.impossible () }
    in
      Just $ Unconditionally label

createTwoValPlan :: S.Set Label -> SwitchTargets -> Integer -> Maybe SwitchPlan
createTwoValPlan labelSet st@(SwitchTargets _ _ defLabelOpt _ _) bitsInWord
  = let  -- Can never fail but let's silence the ghc warning.
      (label1, label2) = case S.toList labelSet of { [lab1, lab2] -> (lab1, lab2); _ -> U.impossible () }
    in
      case defLabelOpt of 
        Just defLabel -> createTwoValPlanWithDefault st (if label1 == defLabel then label2 else label1) bitsInWord
        Nothing -> createBitTwoValPlanNoDefault st label1 label2 bitsInWord

-- Function creates a plan 
createBitTwoValPlanNoDefault :: SwitchTargets -> Label -> Label -> Integer -> Maybe SwitchPlan
createBitTwoValPlanNoDefault
  (SwitchTargets signed range@(lb, ub) _defLabelOpt _intToLabel labelToInts)
  label1
  label2
  bitsInWord
  = let
      label1Ints = case M.lookup label1 labelToInts of { Just ns -> ns; Nothing -> U.impossible () }
      label2Ints = case M.lookup label2 labelToInts of { Just ns -> ns; Nothing -> U.impossible () }

      region1IsDense = U.isDense label1Ints
      region2IsDense = U.isDense label2Ints

      region1Range@(region1Lb, region1Ub) = (head label1Ints, last label1Ints)
      region2Range@(region2Lb, region2Ub) = (head label2Ints, last label2Ints)

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
             Just $ cbp signed doLeftCheckRegion1 lab2PlanOpt doRightCheckRegion1 lab2PlanOpt lab1Plan region1Range

         | region2IsDense && numChecksForRegion2 < 2 ->
             Just $ cbp signed doLeftCheckRegion2 lab1PlanOpt doRightCheckRegion2 lab1PlanOpt lab2Plan region2Range

         | totalSpan <= bitsInWord -> Just $ createBitTestPlan label1 label1Ints lb ub label2 bitsInWord

         | region1IsDense ->
             Just $ cbp signed doLeftCheckRegion1 lab2PlanOpt doRightCheckRegion1 lab2PlanOpt lab1Plan region1Range

         | region2IsDense ->
             Just $ cbp signed doLeftCheckRegion2 lab1PlanOpt doRightCheckRegion2 lab1PlanOpt lab2Plan region2Range

         | region1Count == 2 -> Just $ createEqPlan label1Ints label1 label2

         | region2Count == 2 -> Just $ createEqPlan label2Ints label2 label1

         | otherwise ->
           let
             region1Score = U.ind (span1 > bitsInWord) * 10 + numChecksForRegion1
             region2Score = U.ind (span2 > bitsInWord) * 10 + numChecksForRegion2

             minScore = min region1Score region2Score
           in
             trace (show region1Score ++ " : " ++ show region2Score ++ " : " ++ show span1 ++ " : " ++ show span2) $
             if minScore >= 10
             then
               if | region1Count == 3 -> Just $ createEqPlanFor3 signed label1Ints label1 label2 range
                  | region2Count == 3 -> Just $ createEqPlanFor3 signed label2Ints label2 label1 range
                  | otherwise -> Nothing
             else
               Just $
               if region1Score == minScore
               then cbp signed doLeftCheckRegion1 lab2PlanOpt doRightCheckRegion1 lab2PlanOpt
                        (createBitTestPlan label1 label1Ints region1Lb region1Ub label2 bitsInWord)
                        region1Range
               else cbp signed doLeftCheckRegion2 lab1PlanOpt doRightCheckRegion2 lab1PlanOpt
                        (createBitTestPlan label2 label2Ints region2Lb region2Ub label1 bitsInWord)
                        region2Range

maxExpandSizeForDefaultForTwoValOptimization :: Integer
maxExpandSizeForDefaultForTwoValOptimization = 128

createTwoValPlanWithDefault :: SwitchTargets -> Label -> Integer -> Maybe SwitchPlan
createTwoValPlanWithDefault
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts)
    label
    bitsInWord
  = let
      defLabel = Maybe.fromJust defLabelOpt
      totalSpan = ub - lb + 1

      (intToLabel', labelToInts') = U.eliminateKeyFromMaps defLabel intToLabel labelToInts
    in
      trace "I am here!!!" $
      if totalSpan <= maxExpandSizeForDefaultForTwoValOptimization
      then
        let
          numLabelForDefault = [(i, defLabel) | i <- [lb..ub], not (i `M.member` intToLabel')]

          intToLabel'' = L.foldl' (\m (i, l) -> M.insert i l m) intToLabel' numLabelForDefault
          labelToInts'' = M.insert defLabel (fst <$> numLabelForDefault) labelToInts'
                        
          st' = SwitchTargets signed range Nothing intToLabel'' labelToInts''
        in
          trace (show st') $
           createBitTwoValPlanNoDefault st' label defLabel bitsInWord
      else
        let
          labelInts = case M.lookup label labelToInts' of { Just ns -> ns; Nothing -> U.impossible () }
          regionCount = length labelInts
          regionIsDense = U.isDense labelInts

          regionRange@(regionLb, regionUb) = (head labelInts, last labelInts)

          doLeftCheckRegion = lb < regionLb
          doRightCheckRegion = ub > regionUb

          labPlan = Unconditionally label
          defPlan = Unconditionally defLabel
          defPlanOpt = Just defPlan

          spanOfRegion = regionUb - regionLb + 1
        in
          if | regionCount == 1 -> Just $ IfEqual (head labelInts) label defPlan
             | regionIsDense ->
                 Just $ cbp signed doLeftCheckRegion defPlanOpt doRightCheckRegion defPlanOpt labPlan regionRange
             | regionCount == 2 -> Just $ createEqPlan labelInts label defLabel
             | spanOfRegion <= bitsInWord ->
                 Just $ cbp signed doLeftCheckRegion defPlanOpt doRightCheckRegion defPlanOpt
                            (createBitTestPlan label labelInts regionLb regionUb defLabel bitsInWord)
                            regionRange
             | regionCount == 3 -> Just $ createEqPlanFor3 signed labelInts label defLabel range
             | otherwise -> Nothing

createThreeValPlan :: SwitchTargets -> Integer -> Platform -> Maybe SwitchPlan
createThreeValPlan = createValPlan 3

createFourValPlan :: SwitchTargets -> Integer -> Platform -> Maybe SwitchPlan
createFourValPlan = createValPlan 4

createValPlan :: Int -> SwitchTargets -> Integer -> Platform -> Maybe SwitchPlan
createValPlan
  numVals
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts)
  bitsInWord
  platform
  = case simplePlan of
      Just _ -> simplePlan
      Nothing -> tryBitTestType2Plan signed range bitsInWord defLabelOpt intToLabel' numOfValsForIfStatement labelInts
  where
    numOfValsForIfStatement = numVals - 1

    (intToLabel', labelToInts')
      = case defLabelOpt of
          Just defLabel -> U.eliminateKeyFromMaps defLabel intToLabel labelToInts
          Nothing -> (intToLabel, labelToInts)

    labelInts = M.toList labelToInts'

    simplePlan = U.firstSuccess $ map tryOneLabelElimination labelInts

    tryOneLabelElimination :: (Label, [Integer]) -> Maybe SwitchPlan
    tryOneLabelElimination (lab, labelCases)
      = case labelCases of
          [n] | n == lb || n == ub
            -> let
                  intToLabel'' = M.delete n intToLabel'
                  labelToInts'' = M.delete lab labelToInts'
                  range' = if n == lb then (lb + 1, ub) else (lb, ub - 1)
                  st' = SwitchTargets signed range' defLabelOpt intToLabel'' labelToInts''
                  elsePlan = createPlan st' platform
                in Just $ createEqPlanWithPlan labelCases lab elsePlan
          _ -> Nothing

tryBitTestType2Plan :: Bool -> (Integer, Integer) -> Integer -> Maybe Label
                      -> M.Map Integer Label -> Int -> [(Label, [Integer])] -> Maybe SwitchPlan
tryBitTestType2Plan signed (lb, ub) bitsInWord defLabelOpt intToLabel numOfValsForIfStatement labelInts
  = let
      totalSpan = ub - lb + 1
    in
      trace (show totalSpan) $
      if 2 * totalSpan <= bitsInWord
      then Just $ buildPlanForTotalSpan ()
      else
        let
          (mn, _) = M.findMin intToLabel
          (mx, _) = M.findMax intToLabel
          regionSpan = mx - mn + 1
        in
          trace (show regionSpan) $
          if 2 * regionSpan <= bitsInWord
          then Just $ buildPlanForPartialSpan mn mx
          else Nothing
  where
    buildPlanForTotalSpan :: () -> SwitchPlan
    buildPlanForTotalSpan () = fst $ buildPlanForBitTestType2 numOfValsForIfStatement lb ub defLabelOpt bitsInWord labelInts

    buildPlanForPartialSpan :: Integer -> Integer -> SwitchPlan
    buildPlanForPartialSpan regionLb regionUb
      = let
          (bitTestPlan, bitTestFailedPlan) = buildPlanForBitTestType2 numOfValsForIfStatement regionLb regionUb defLabelOpt bitsInWord labelInts
          doLeftCheck = lb < regionLb
          doRightCheck = ub > regionUb

          failedPlanOpt = Just bitTestFailedPlan
        in
          cbp signed doLeftCheck failedPlanOpt doRightCheck failedPlanOpt bitTestPlan (regionLb, regionUb)

buildPlanForBitTestType2 :: Int -> Integer -> Integer -> Maybe Label -> Integer -> [(Label, [Integer])] -> (SwitchPlan, SwitchPlan)
buildPlanForBitTestType2 numberOfLabelsForPlan regionLb regionUb defLabelOpt bitsInWord ls
  = let
      sortedOnLength = L.sortOn (negate . length . snd) ls
      labelsForTest = L.take numberOfLabelsForPlan sortedOnLength
      nns = L.map snd labelsForTest

      canSkipOffset = regionLb >= 0 && 2 * regionUb < bitsInWord
      (offset2, constants) = if canSkipOffset then (Nothing, nns)
                             else (Just regionLb, L.map (L.map (\n -> n - regionLb)) nns)

      (magicConstant2, bitPatterns) = U.calcMagicConstant2 constants
      testFailedLabel = case defLabelOpt of { Just l -> l; Nothing -> fst $ last sortedOnLength }
      bitTestFailedPlan = Unconditionally testFailedLabel
      bitTestType2Info = BitTestType2Info { offset2 = offset2, magicConstant2 = magicConstant2, bitTestFailedPlan2 = bitTestFailedPlan }
      intLabels = zip bitPatterns (L.map fst labelsForTest)
    in
      trace ("numlabelsforplan: " ++ show numberOfLabelsForPlan) $
      trace (show sortedOnLength)
      (BitTestType2 bitTestType2Info intLabels, bitTestFailedPlan)

pNumerator :: Int
pNumerator = 1

pDenominator :: Int
pDenominator = 2

maxJumpTableGapSize :: Integer
maxJumpTableGapSize = 6

minJumpTableSize :: Int
minJumpTableSize = 5

minJumpTableOffset :: Integer
minJumpTableOffset = 2

maxExpandSizeForDefaultForJumpTableOptimization :: Integer
maxExpandSizeForDefaultForJumpTableOptimization = 64

createJumpTable :: SwitchTargets -> Maybe SwitchPlan
createJumpTable st@(SwitchTargets _signed (lb, ub) defLabelOpt intToLabel _labelToInts)
  = if | Just _ <- defLabelOpt
       -> let
            spanOfFullRegion = ub - lb + 1
          in
            if spanOfFullRegion <= maxExpandSizeForDefaultForJumpTableOptimization
            then createJumpTableAux (expandRegion st lb ub) True
            else
              let
                (regionLb, _) = M.findMin intToLabel
                (regionUb, _) = M.findMax intToLabel
                spanOfCases = regionUb - regionLb + 1
              in
                if spanOfCases <= maxExpandSizeForDefaultForJumpTableOptimization
                then createJumpTableAux (expandRegion st regionLb regionUb) True
                else createJumpTableAux st False
       | otherwise -> createJumpTableAux st True

createJumpTableAux :: SwitchTargets -> Bool -> Maybe SwitchPlan
createJumpTableAux st@(SwitchTargets _signed _range _defLabelOpt intToLabel _labelToInts) hasBeenExpanded
  = let
      numCases = M.size intToLabel
    in
      if | numCases < minJumpTableSize -> Nothing
         | hasBeenExpanded || U.isDenseEnough maxJumpTableGapSize (M.keys intToLabel) -> Just $ JumpTable st
         | otherwise -> Nothing

splitInterval :: SwitchTargets -> (SwitchTargets, Integer, SwitchTargets)
splitInterval (SwitchTargets signed (lb, ub) defLabelOpt intToLabel _labelToInts)
  = let
      caseInts = M.keys intToLabel
      regionSeparators = U.findRegionSeparators maxJumpTableGapSize caseInts
      midSeparator = U.findMiddleOfList regionSeparators

      (intToLabelLeft, intToLabelRight) = U.splitMap midSeparator intToLabel U.RightMap

      leftUb = midSeparator - 1
      rightLb = midSeparator

      defLabelLeft = if lb == leftUb then Nothing else defLabelOpt
      defLabelRight = if rightLb == ub then Nothing else defLabelOpt

      stLeft = mkSwitchTargets signed (lb, leftUb) defLabelLeft intToLabelLeft
      stRight = mkSwitchTargets signed (rightLb, ub) defLabelRight intToLabelRight
    in
      trace ("stLeft: " ++ show stLeft) $
      trace ("stRight: " ++ show stRight) $
      trace ("separator: " ++ show midSeparator)

      (stLeft, midSeparator, stRight)

expandRegion :: SwitchTargets -> Integer -> Integer -> SwitchTargets
expandRegion (SwitchTargets signed range@(lb, ub) defLabelOpt@(Just defLabel) intToLabel labelToInts) regLb regUb
  = let
      (intToLabel', labelToInts') = U.eliminateKeyFromMaps defLabel intToLabel labelToInts
      numCasesForDefault = [(i, defLabel) | i <- [regLb..regUb], not (i `M.member` intToLabel')]

      intToLabel'' = L.foldl' (\m (i, l) -> M.insert i l m) intToLabel' numCasesForDefault
      labelToInts'' = M.insert defLabel (fst <$> numCasesForDefault) labelToInts'

      defl = if regLb == lb && regUb == ub then Nothing else defLabelOpt
    in
      SwitchTargets signed range defl intToLabel'' labelToInts''

expandRegion (SwitchTargets _ _ Nothing _ _) _ _ = U.impossible ()

cbp :: Bool -> Bool -> Maybe SwitchPlan -> Bool -> Maybe SwitchPlan -> SwitchPlan 
       -> (Integer, Integer) -> SwitchPlan
cbp signed doLeftCheck leftPlan doRightCheck rightPlan
  = createBracketPlan
      signed
      (if doLeftCheck then leftPlan else Nothing)
      (if doRightCheck then rightPlan else Nothing)

createEqPlan :: [Integer] -> Label -> Label -> SwitchPlan
createEqPlan labelInts lab1 lab2
  = createEqPlanWithPlan labelInts lab1 (Unconditionally lab2)

createEqPlanWithPlan :: [Integer] -> Label -> SwitchPlan -> SwitchPlan
createEqPlanWithPlan labelInts thenLabel elsePlan
  = F.foldr' (`IfEqual` thenLabel) elsePlan labelInts

createEqPlanFor3 :: Bool -> [Integer] -> Label -> Label -> (Integer, Integer) -> SwitchPlan
createEqPlanFor3 signed labelInts lab1 lab2 (lb, ub)
  = let
      (n0, n1, n2) = case labelInts of {[x0, x1, x2] -> (x0, x1, x2); _ -> U.impossible () }
      lab1Plan = Unconditionally lab1
      lab2Plan = Unconditionally lab2
    in
      if | n0 == lb && n0 + 1 == n1 -> IfLE signed n1 lab1Plan (IfEqual n2 lab1 lab2Plan)
         | n2 == ub && n2 - 1 == n1 -> IfLT signed n1 (IfEqual n0 lab1 lab2Plan) lab1Plan
         | otherwise -> createEqPlan labelInts lab1 lab2

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
                     -> (Integer, Integer) -> SwitchPlan
createBracketPlan signed leftBracketPlanOpt rightBracketPlanOpt bitTestPlan (lb, ub)
  = case (leftBracketPlanOpt, rightBracketPlanOpt) of

      (Just leftPlan, Just rightPlan) -> IfLT signed lb leftPlan (IfLE signed ub bitTestPlan rightPlan)

      (Just leftPlan, Nothing) -> IfLT signed lb leftPlan bitTestPlan

      (Nothing, Just rightPlan) -> IfLE signed ub bitTestPlan rightPlan

      (Nothing, Nothing) -> bitTestPlan
