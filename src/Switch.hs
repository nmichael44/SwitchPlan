{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}

module Switch where

import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Map.Lazy as M
import qualified Data.Maybe as Maybe
import qualified Data.Set as S
import Debug.Trace
import qualified SwitchUtils as U

data SwitchTargets
  = SwitchTargets
      Bool -- Signed values
      (Integer, Integer) -- Range
      (Maybe Label) -- Default value
      (M.Map Integer Label) -- The branches
      (M.Map Label [Integer]) -- The reverse of the above Map
  deriving (Show, Eq)

getSigned :: SwitchTargets -> Bool
getSigned (SwitchTargets signed _ _ _ _) = signed

getDefLabel :: SwitchTargets -> Maybe Label
getDefLabel (SwitchTargets _ _ defLabelOpt _ _) = defLabelOpt

getLabelToInts :: SwitchTargets -> M.Map Label [Integer]
getLabelToInts (SwitchTargets _ _ _ _ labelToInts) = labelToInts

mkSwitchTargets :: Bool -> (Integer, Integer) -> Maybe Label -> M.Map Integer Label -> SwitchTargets
mkSwitchTargets signed range defLabel intToLabel =
  SwitchTargets signed range defLabel intToLabel (U.calcRevMap intToLabel)

newtype Label = L Integer
  deriving (Eq, Ord)

instance Show Label where
  show :: Label -> String
  show (L n) = "L" ++ show n

bytesInWordForPlatform :: Int
bytesInWordForPlatform = 8

bitsInWordForPlatform :: Int
bitsInWordForPlatform = bytesInWordForPlatform * 8

data BitTestInfo = BitTestInfo
  { offset :: Maybe Integer,
    magicConstant :: Integer,
    bitTestFailedPlan :: SwitchPlan
  }

data BitTestType2Info = BitTestType2Info
  { offset2 :: Maybe Integer,
    magicConstant2 :: Integer,
    bitTestFailedPlan2 :: SwitchPlan
  }

data SwitchPlan
  = Unconditionally Label
  | IfEqual Integer Label SwitchPlan
  | IfLT Bool Integer SwitchPlan SwitchPlan
  | IfLE Bool Integer SwitchPlan SwitchPlan
  | BitTest BitTestInfo SwitchPlan
  | BitTestType2 BitTestType2Info [(Integer, Label)]
  | JumpTable SwitchTargets
  deriving (Show)

instance Show BitTestInfo where
  show :: BitTestInfo -> String
  show BitTestInfo {offset, magicConstant, bitTestFailedPlan} =
    "BitTestInfo { offset = " ++ show offset
      ++ ", magicConst = "
      ++ U.convIntegerToBinary bitsInWordForPlatform magicConstant
      ++ ", bitTestFailedPlan = "
      ++ show bitTestFailedPlan
      ++ " }"

instance Show BitTestType2Info where
  show :: BitTestType2Info -> String
  show BitTestType2Info {offset2, magicConstant2, bitTestFailedPlan2} =
    "BitTestType2Info { offset2 = " ++ show offset2
      ++ ", magicConst2 = "
      ++ U.convIntegerToBinary bitsInWordForPlatform magicConstant2
      ++ ", bitTestFailedPlan2 = "
      ++ show bitTestFailedPlan2
      ++ " }"

newtype Platform = Platform Int

platformWordSizeInBytes :: Platform -> Int
platformWordSizeInBytes (Platform n) = n

switchTableEnabled :: Bool
switchTableEnabled = False

createPlan :: SwitchTargets -> Platform -> SwitchPlan
createPlan st platform =
  let -- We have to do this because one of the integer labels could be the same as the default label
      -- Thus we build a set to remove possible duplicates.
      labelSet = let s = M.keysSet (getLabelToInts st) in maybe s (`S.insert` s) (getDefLabel st)
      numLabels = S.size labelSet
      bitsInWord = 8 * fromIntegral (platformWordSizeInBytes platform)
   in trace ("NumLabels: " ++ show numLabels) $
        if
            | numLabels == 1,
              Just plan <- createOneValPlan labelSet ->
              trace "1!!!" plan
            | numLabels == 2,
              Just plan <- createTwoValPlan labelSet st bitsInWord ->
              trace "2!!!" plan
            | numLabels == 3,
              Just plan <- createThreeValPlan st bitsInWord platform ->
              trace "3!!!" plan
            | numLabels == 4,
              Just plan <- createFourValPlan st bitsInWord platform ->
              trace "4!!!" plan
            | switchTableEnabled,
              Just plan <- createJumpTable st ->
              trace "5!!!" plan
            | otherwise ->
              trace "6!!!" $ createSplitPlan (getSigned st) (splitInterval st) platform

createSplitPlan :: Bool -> (SwitchTargets, Integer, SwitchTargets) -> Platform -> SwitchPlan
createSplitPlan signed (stLeft, n, stRight) platform =
  IfLT signed n (createPlan stLeft platform) (createPlan stRight platform)

createOneValPlan :: S.Set Label -> Maybe SwitchPlan
createOneValPlan labelSet =
  let label = case S.toList labelSet of [l] -> l; _ -> U.impossible ()
   in Just $ Unconditionally label

createTwoValPlan :: S.Set Label -> SwitchTargets -> Integer -> Maybe SwitchPlan
createTwoValPlan labelSet st@(SwitchTargets _ _ defLabelOpt _ _) bitsInWord =
  let -- Can never fail but let's silence the ghc warning.
      (label1, label2) = case S.toList labelSet of [lab1, lab2] -> (lab1, lab2); _ -> U.impossible ()
   in case defLabelOpt of
        Just defLabel -> createTwoValPlanWithDefault st (if label1 == defLabel then label2 else label1) bitsInWord
        Nothing -> createBitTwoValPlanNoDefault st label1 label2 bitsInWord

-- Function creates a plan
createBitTwoValPlanNoDefault :: SwitchTargets -> Label -> Label -> Integer -> Maybe SwitchPlan
createBitTwoValPlanNoDefault
  (SwitchTargets signed range@(lb, ub) _defLabelOpt _intToLabel labelToInts)
  label1
  label2
  bitsInWord =
    let label1Ints = case M.lookup label1 labelToInts of Just ns -> ns; Nothing -> U.impossible ()
        label2Ints = case M.lookup label2 labelToInts of Just ns -> ns; Nothing -> U.impossible ()

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
     in if
            | region1Count == 1 -> Just $ IfEqual region1Lb label1 lab2Plan
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
              let region1Score = U.ind (span1 > bitsInWord) * 10 + numChecksForRegion1
                  region2Score = U.ind (span2 > bitsInWord) * 10 + numChecksForRegion2

                  minScore = min region1Score region2Score
               in trace (show region1Score ++ " : " ++ show region2Score ++ " : " ++ show span1 ++ " : " ++ show span2) $
                    if minScore >= 10
                      then
                        if
                            | region1Count == 3 -> Just $ createEqPlanFor3 signed label1Ints label1 label2 range
                            | region2Count == 3 -> Just $ createEqPlanFor3 signed label2Ints label2 label1 range
                            | otherwise -> Nothing
                      else
                        Just $
                          if region1Score == minScore
                            then
                              cbp
                                signed
                                doLeftCheckRegion1
                                lab2PlanOpt
                                doRightCheckRegion1
                                lab2PlanOpt
                                (createBitTestPlan label1 label1Ints region1Lb region1Ub label2 bitsInWord)
                                region1Range
                            else
                              cbp
                                signed
                                doLeftCheckRegion2
                                lab1PlanOpt
                                doRightCheckRegion2
                                lab1PlanOpt
                                (createBitTestPlan label2 label2Ints region2Lb region2Ub label1 bitsInWord)
                                region2Range

maxExpandSizeForDefaultForTwoValOptimization :: Integer
maxExpandSizeForDefaultForTwoValOptimization = 128

createTwoValPlanWithDefault :: SwitchTargets -> Label -> Integer -> Maybe SwitchPlan
createTwoValPlanWithDefault
  (SwitchTargets signed range@(lb, ub) defLabelOpt intToLabel labelToInts)
  label
  bitsInWord =
    let defLabel = Maybe.fromJust defLabelOpt
        totalSpan = ub - lb + 1

        (intToLabel', labelToInts') = U.eliminateKeyFromMaps defLabel intToLabel labelToInts
     in trace "I am here!!!" $
          if totalSpan <= maxExpandSizeForDefaultForTwoValOptimization
            then
              let numLabelForDefault = [(i, defLabel) | i <- [lb .. ub], not (i `M.member` intToLabel')]

                  intToLabel'' = L.foldl' (\m (i, l) -> M.insert i l m) intToLabel' numLabelForDefault
                  labelToInts'' = M.insert defLabel (fst <$> numLabelForDefault) labelToInts'

                  st' = SwitchTargets signed range Nothing intToLabel'' labelToInts''
               in trace (show st') $
                    createBitTwoValPlanNoDefault st' label defLabel bitsInWord
            else
              let labelInts = case M.lookup label labelToInts' of Just ns -> ns; Nothing -> U.impossible ()
                  regionCount = length labelInts
                  regionIsDense = U.isDense labelInts

                  regionRange@(regionLb, regionUb) = (head labelInts, last labelInts)

                  doLeftCheckRegion = lb < regionLb
                  doRightCheckRegion = ub > regionUb

                  labPlan = Unconditionally label
                  defPlan = Unconditionally defLabel
                  defPlanOpt = Just defPlan

                  spanOfRegion = regionUb - regionLb + 1
               in if
                      | regionCount == 1 -> Just $ IfEqual (head labelInts) label defPlan
                      | regionIsDense ->
                        Just $ cbp signed doLeftCheckRegion defPlanOpt doRightCheckRegion defPlanOpt labPlan regionRange
                      | regionCount == 2 -> Just $ createEqPlan labelInts label defLabel
                      | spanOfRegion <= bitsInWord ->
                        Just $
                          cbp
                            signed
                            doLeftCheckRegion
                            defPlanOpt
                            doRightCheckRegion
                            defPlanOpt
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
  platform =
    case simplePlan of
      Just _ -> simplePlan
      Nothing -> tryBitTestType2Plan signed range bitsInWord defLabelOpt intToLabel' numOfValsForIfStatement labelInts
    where
      numOfValsForIfStatement = numVals - 1

      (intToLabel', labelToInts') =
        case defLabelOpt of
          Just defLabel -> U.eliminateKeyFromMaps defLabel intToLabel labelToInts
          Nothing -> (intToLabel, labelToInts)

      labelInts = M.toList labelToInts'

      simplePlan = U.firstSuccess $ map tryOneLabelElimination labelInts

      tryOneLabelElimination :: (Label, [Integer]) -> Maybe SwitchPlan
      tryOneLabelElimination (lab, labelCases) =
        case labelCases of
          [n]
            | n == lb || n == ub ->
              let intToLabel'' = M.delete n intToLabel'
                  labelToInts'' = M.delete lab labelToInts'
                  range' = if n == lb then (lb + 1, ub) else (lb, ub - 1)
                  st' = SwitchTargets signed range' defLabelOpt intToLabel'' labelToInts''
                  elsePlan = createPlan st' platform
               in Just $ createEqPlanWithPlan labelCases lab elsePlan
          _ -> Nothing

tryBitTestType2Plan ::
  Bool ->
  (Integer, Integer) ->
  Integer ->
  Maybe Label ->
  M.Map Integer Label ->
  Int ->
  [(Label, [Integer])] ->
  Maybe SwitchPlan
tryBitTestType2Plan signed (lb, ub) bitsInWord defLabelOpt intToLabel numOfValsForIfStatement labelInts =
  let totalSpan = ub - lb + 1
   in trace (show totalSpan) $
        if 2 * totalSpan <= bitsInWord
          then Just $ buildPlanForTotalSpan ()
          else
            let (mn, _) = M.findMin intToLabel
                (mx, _) = M.findMax intToLabel
                regionSpan = mx - mn + 1
             in trace (show regionSpan) $
                  if 2 * regionSpan <= bitsInWord
                    then Just $ buildPlanForPartialSpan mn mx
                    else Nothing
  where
    buildPlanForTotalSpan :: () -> SwitchPlan
    buildPlanForTotalSpan () = fst $ buildPlanForBitTestType2 numOfValsForIfStatement lb ub defLabelOpt bitsInWord labelInts

    buildPlanForPartialSpan :: Integer -> Integer -> SwitchPlan
    buildPlanForPartialSpan regionLb regionUb =
      let (bitTestPlan, bitTestFailedPlan) = buildPlanForBitTestType2 numOfValsForIfStatement regionLb regionUb defLabelOpt bitsInWord labelInts
          doLeftCheck = lb < regionLb
          doRightCheck = ub > regionUb

          failedPlanOpt = Just bitTestFailedPlan
       in cbp signed doLeftCheck failedPlanOpt doRightCheck failedPlanOpt bitTestPlan (regionLb, regionUb)

buildPlanForBitTestType2 :: Int -> Integer -> Integer -> Maybe Label -> Integer -> [(Label, [Integer])] -> (SwitchPlan, SwitchPlan)
buildPlanForBitTestType2 numberOfLabelsForPlan regionLb regionUb defLabelOpt bitsInWord ls =
  let sortedOnLength = L.sortOn (negate . length . snd) ls
      labelsForTest = L.take numberOfLabelsForPlan sortedOnLength
      nns = L.map snd labelsForTest

      canSkipOffset = regionLb >= 0 && 2 * regionUb < bitsInWord
      (offset2, constants) =
        if canSkipOffset
          then (Nothing, nns)
          else (Just regionLb, L.map (L.map (\n -> n - regionLb)) nns)

      (magicConstant2, bitPatterns) = U.calcMagicConstant2 constants
      testFailedLabel = case defLabelOpt of Just l -> l; Nothing -> fst $ last sortedOnLength
      bitTestFailedPlan = Unconditionally testFailedLabel
      bitTestType2Info = BitTestType2Info {offset2 = offset2, magicConstant2 = magicConstant2, bitTestFailedPlan2 = bitTestFailedPlan}
      intLabels = zip bitPatterns (L.map fst labelsForTest)
   in trace ("numlabelsforplan: " ++ show numberOfLabelsForPlan) $
        trace
          (show sortedOnLength)
          (BitTestType2 bitTestType2Info intLabels, bitTestFailedPlan)

pNumerator :: Int
pNumerator = 1

pDenominator :: Int
pDenominator = 2

maxJumpTableHole :: Integer
maxJumpTableHole = 7

minJumpTableSize :: Int
minJumpTableSize = 5

minJumpTableOffset :: Integer
minJumpTableOffset = 2

maxExpandSizeForDefaultForJumpTableOptimization :: Integer
maxExpandSizeForDefaultForJumpTableOptimization = 64

createJumpTable :: SwitchTargets -> Maybe SwitchPlan
createJumpTable st@(SwitchTargets _signed (lb, ub) defLabelOpt intToLabel _labelToInts) =
  if
      | Just _ <- defLabelOpt ->
        let spanOfFullRegion = ub - lb + 1
         in if spanOfFullRegion <= maxExpandSizeForDefaultForJumpTableOptimization
              then createJumpTableAux (expandRegion st lb ub) True
              else
                let (regionLb, _) = M.findMin intToLabel
                    (regionUb, _) = M.findMax intToLabel
                    spanOfCases = regionUb - regionLb + 1
                 in if spanOfCases <= maxExpandSizeForDefaultForJumpTableOptimization
                      then createJumpTableAux (expandRegion st regionLb regionUb) True
                      else createJumpTableAux st False
      | otherwise -> createJumpTableAux st True

createJumpTableAux :: SwitchTargets -> Bool -> Maybe SwitchPlan
createJumpTableAux st@(SwitchTargets _signed _range _defLabelOpt intToLabel _labelToInts) hasBeenExpanded =
  let numCases = M.size intToLabel
   in if
          | numCases < minJumpTableSize -> Nothing
          | hasBeenExpanded || U.isDenseEnough maxJumpTableHole (M.keys intToLabel) -> Just $ JumpTable st
          | otherwise -> Nothing

splitInterval :: SwitchTargets -> (SwitchTargets, Integer, SwitchTargets)
splitInterval (SwitchTargets signed (lb, ub) defLabelOpt intToLabel _labelToInts) =
  let caseInts = M.keys intToLabel
      regionSeparators = U.findRegionSeparators maxJumpTableHole caseInts
      midSeparator = U.findMiddleOfList regionSeparators

      (intToLabelLeft, intToLabelRight) = U.splitMap midSeparator intToLabel U.RightMap

      leftUb = midSeparator - 1
      rightLb = midSeparator

      defLabelLeft = if lb == leftUb then Nothing else defLabelOpt
      defLabelRight = if rightLb == ub then Nothing else defLabelOpt

      stLeft = mkSwitchTargets signed (lb, leftUb) defLabelLeft intToLabelLeft
      stRight = mkSwitchTargets signed (rightLb, ub) defLabelRight intToLabelRight
   in trace ("stLeft: " ++ show stLeft) $
        trace ("stRight: " ++ show stRight) $
          trace
            ("separator: " ++ show midSeparator)
            (stLeft, midSeparator, stRight)

expandRegion :: SwitchTargets -> Integer -> Integer -> SwitchTargets
expandRegion (SwitchTargets signed range@(lb, ub) defLabelOpt@(Just defLabel) intToLabel labelToInts) regLb regUb =
  let (intToLabel', labelToInts') = U.eliminateKeyFromMaps defLabel intToLabel labelToInts
      numCasesForDefault = [(i, defLabel) | i <- [regLb .. regUb], not (i `M.member` intToLabel')]

      intToLabel'' = L.foldl' (\m (i, l) -> M.insert i l m) intToLabel' numCasesForDefault
      labelToInts'' = M.insert defLabel (fst <$> numCasesForDefault) labelToInts'

      defl = if regLb == lb && regUb == ub then Nothing else defLabelOpt
   in SwitchTargets signed range defl intToLabel'' labelToInts''
expandRegion (SwitchTargets _ _ Nothing _ _) _ _ = U.impossible ()

cbp :: Bool -> Bool -> Maybe SwitchPlan -> Bool -> Maybe SwitchPlan
       -> SwitchPlan -> (Integer, Integer) -> SwitchPlan
cbp signed doLeftCheck leftPlan doRightCheck rightPlan =
  createBracketPlan
    signed
    (if doLeftCheck then leftPlan else Nothing)
    (if doRightCheck then rightPlan else Nothing)

createEqPlan :: [Integer] -> Label -> Label -> SwitchPlan
createEqPlan labelInts lab1 lab2 =
  createEqPlanWithPlan labelInts lab1 (Unconditionally lab2)

createEqPlanWithPlan :: [Integer] -> Label -> SwitchPlan -> SwitchPlan
createEqPlanWithPlan labelInts thenLabel elsePlan =
  F.foldr' (`IfEqual` thenLabel) elsePlan labelInts

createEqPlanFor3 :: Bool -> [Integer] -> Label -> Label -> (Integer, Integer) -> SwitchPlan
createEqPlanFor3 signed labelInts lab1 lab2 (lb, ub) =
  let (n0, n1, n2) = case labelInts of [x0, x1, x2] -> (x0, x1, x2); _ -> U.impossible ()
      lab1Plan = Unconditionally lab1
      lab2Plan = Unconditionally lab2
   in if
          | n0 == lb && n0 + 1 == n1 -> IfLE signed n1 lab1Plan (IfEqual n2 lab1 lab2Plan)
          | n2 == ub && n2 - 1 == n1 -> IfLT signed n1 (IfEqual n0 lab1 lab2Plan) lab1Plan
          | otherwise -> createEqPlan labelInts lab1 lab2

createBitTestPlan :: Label -> [Integer] -> Integer -> Integer -> Label -> Integer -> SwitchPlan
createBitTestPlan bitTestLabel intsOfLabel regionLb regionUb otherLabel bitsInWord =
  let canSkipOffset = regionLb >= 0 && regionUb < bitsInWord
      (offset, constants) =
        if canSkipOffset
          then (Nothing, intsOfLabel)
          else (Just regionLb, (\n -> n - regionLb) <$> intsOfLabel)
      magicConstant = U.calcMagicConstant constants bitsInWord
      otherLabelPlan = Unconditionally otherLabel
      bitTestInfo =
        BitTestInfo
          { offset = offset,
            magicConstant = magicConstant,
            bitTestFailedPlan = otherLabelPlan
          }
   in BitTest bitTestInfo $ Unconditionally bitTestLabel

createBracketPlan :: Bool -> Maybe SwitchPlan -> Maybe SwitchPlan -> SwitchPlan
                     -> (Integer, Integer) -> SwitchPlan
createBracketPlan signed leftBracketPlanOpt rightBracketPlanOpt bitTestPlan (lb, ub) =
  case (leftBracketPlanOpt, rightBracketPlanOpt) of
    (Just leftPlan, Just rightPlan) -> IfLT signed lb leftPlan (IfLE signed ub bitTestPlan rightPlan)
    (Just leftPlan, Nothing) -> IfLT signed lb leftPlan bitTestPlan
    (Nothing, Just rightPlan) -> IfLE signed ub bitTestPlan rightPlan
    (Nothing, Nothing) -> bitTestPlan

-------------------------------------------------------------

tr :: Show a => a -> b -> b
tr obj = trace (show obj)

type IntLabel = (Integer, Label)

data SegmentType
  = IsolatedValues {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , casesAreDense :: Bool
    , cases :: [IntLabel]
    }
  | TwoLabelsType1 {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , casesAreDense :: Bool
    , casesForTest :: [IntLabel] -- this is allowed to be empty.  In that case go to otherLabel unconditionally.
    , casesForTestSize :: Int
    , otherLabel :: Label
    }
  | TwoLabelsType2 {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , casesForTest :: [IntLabel]
    , lbForTest :: Integer
    , ubForTest :: Integer
    , casesAreDense :: Bool
    , casesForTestSize :: Int
    , otherLabel :: Label
    }
  | FourLabels {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , cases :: [IntLabel]
    }
  | MultiWayJump {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , casesAreDense :: Bool
    , cases :: [IntLabel]
    }
  deriving (Show, Eq)

type SegmentTypeWithSize = (Int, SegmentType)

{-
  Returns the first n labels along with their int cases (plus min and max) up to
  the point when it encounters the n + 1 label.

  For example for numLabels == 2 and map as below:

  1 -> L1
  2 -> L2
  3 -> L1
  4 -> L1
  5 -> L3
  6 -> L1

  it returns the pair:
  (fromList [(L1,(1,4,[1,3,4])),(L2,(2,2,[2]))]
   , [(6,L1)])
  Note that it does not return 6 for L1 in the map since it occurs after]
  we have seen the third label (L3).  
-}
findFirstNLabels :: Int -> [IntLabel] -> M.Map Label [Integer]
                    -> (M.Map Label (Integer, Integer, [Integer]), [IntLabel])
findFirstNLabels numLabels xs m
  = let
      (labToInts, rest) = go xs m
    in
      (M.map computeTriplet labToInts, rest)
  where
    computeTriplet :: [Integer] -> (Integer, Integer, [Integer])
    computeTriplet ns
      = let
          rev = reverse ns
        in
          (head rev, head ns, rev)

    go :: [IntLabel] -> M.Map Label [Integer]-> (M.Map Label [Integer], [IntLabel])
    go [] m = (m, [])
    go ((n, lab) : rest) m
      = let
          m' = M.insertWith (++) lab [n] m
        in
          if M.size m' <= numLabels
          then go rest m'
          else (m, rest)

minBitTestSize :: Int
minBitTestSize = 4

mergeConsecutiveIsolatedSegments :: [SegmentType] -> [SegmentType]
mergeConsecutiveIsolatedSegments
  = L.foldr mergeSegments []  -- foldr here avoids an O(n^2) cost with the append of the 'cases' lists.
  where
    mergeSegments :: SegmentType -> [SegmentType] -> [SegmentType]
    mergeSegments IsolatedValues { segSize = segSize1, segLb = segLb1, segUb = segUb1, casesAreDense = casesAreDense1, cases = cases1 }
                  (IsolatedValues { segSize = segSize2, segLb = segLb2, segUb = segUb2, casesAreDense = casesAreDense2, cases = cases2 } : rest)
      = IsolatedValues {
          segSize = segSize1 + segSize2
        , segLb = segLb1
        , segUb = segUb2
        , casesAreDense = casesAreDense1
                          && casesAreDense2
                          && segUb1 + 1 == segLb2
        , cases = cases1 ++ cases2
        } : rest
    mergeSegments segment segments = segment : segments

getTwoLabelsType1Segment :: Integer -> [IntLabel] -> Maybe Label
                            -> Maybe (SegmentType, [IntLabel])
getTwoLabelsType1Segment bitsInWord intLabelList defOpt
  = go (tail intLabelList) labelSet 1 startNum True casesForTestInitial casesForTestSizeInitial
  where
    startIntLabel@(startNum, startLabel) = head intLabelList
    labelSet = S.insert startLabel (maybe S.empty S.singleton defOpt)
    otherLabel = Maybe.fromMaybe startLabel defOpt

    (casesForTestInitial, casesForTestSizeInitial)
      = if startLabel == otherLabel then ([], 0)
                                    else ([startIntLabel], 1)

    go :: [IntLabel] -> S.Set Label -> Int -> Integer -> Bool -> [IntLabel] -> Int
          -> Maybe (SegmentType, [IntLabel])
    go [] _ segSize segUb isDense casesForTest casesForTestSize
      = if segSize < minBitTestSize
        then Nothing
        else Just (TwoLabelsType1 {
                    segSize = segSize
                  , segLb = startNum
                  , segUb = segUb
                  , casesAreDense = isDense
                  , casesForTest = L.reverse casesForTest
                  , casesForTestSize = casesForTestSize
                  , otherLabel = otherLabel
                  }, [])

    go xs@(p@(n, lab) : restIntLabel) labSet segSize segUb isDense casesForTest casesForTestSize
      = let
          totalSpan = n - startNum + 1
          labSet' = S.insert lab labSet
        in
          if totalSpan > bitsInWord || S.size labSet' > 2
          then
            if segSize < minBitTestSize
            then Nothing
            else Just (TwoLabelsType1 {
                        segSize = segSize
                      , segLb = startNum
                      , segUb = segUb
                      , casesAreDense = isDense
                      , casesForTest = L.reverse casesForTest
                      , casesForTestSize = casesForTestSize
                      , otherLabel = otherLabel
                      }, xs)
          else
            let
              segSize' = segSize + 1
              segUb' = n
              (casesForTest', isDense', casesForTestSize')
                = if lab == otherLabel
                  then (casesForTest, isDense, casesForTestSize)
                  else (p : casesForTest,
                        isDense && (L.null casesForTest || n == fst (head casesForTest) + 1),
                        casesForTestSize + 1)
            in
              go restIntLabel
                 labSet'
                 segSize'
                 segUb'
                 isDense'
                 casesForTest'
                 casesForTestSize'

getTwoLabelsType2Segment :: Integer -> [IntLabel] -> Maybe Label
                            -> Maybe (SegmentType, [IntLabel])
getTwoLabelsType2Segment bitsInWord intLabelList defOpt
  = undefined 
  where
    bitsLimit = bitsInWord `div` 2

    startIntLabel@(startNum, startLabel) = head intLabelList
    labelSet = S.insert startLabel (maybe S.empty S.singleton defOpt)
    otherLabel = Maybe.fromMaybe startLabel defOpt

    calcOtherLabel (Just (lab2, _, _, _, _, _)) = lab2
    calcOtherLabel Nothing = if Maybe.isJust defOpt then Maybe.fromJust defOpt else U.impossible ()

    go :: [IntLabel]                                                 -- the input
          -> Int                                                     -- Segment size
          -> Integer                                                 -- Segment upper bound
          -> Maybe (Label, Int, Bool, Integer, Integer, [IntLabel])  -- First label info (label, segSize, isDense, lb, ub)
          -> Maybe (Label, Int, Bool, Integer, Integer, [IntLabel])  -- Second label info (label, segSize, isDense, lb, ub)
          -> Maybe (SegmentType, [IntLabel])
    go [] segSize segUb lab1InfoOpt lab2InfoOpt
      = if | Just (lab1, segSize1, isDense1, lb1, ub1, casesForTest1) <- lab1InfoOpt
             , segSize1 < minBitTestSize
             , (Maybe.isNothing defOpt || lab1 /= Maybe.fromJust defOpt)
           -> Just (TwoLabelsType2 {
                      segSize = segSize
                    , segLb = startNum
                    , segUb = segUb
                    , casesForTest = L.reverse casesForTest1
                    , lbForTest = lb1
                    , ubForTest = ub1
                    , casesAreDense = isDense1
                    , casesForTestSize = segSize1
                    , otherLabel = calcOtherLabel lab2InfoOpt
                    }, [])
           | Just (lab2, segSize2, isDense2, lb2, ub2, casesForTest2) <- lab2InfoOpt
             , segSize2 < minBitTestSize
             , (Maybe.isNothing defOpt || lab2 /= Maybe.fromJust defOpt)
           -> Just (TwoLabelsType2 {
                    segSize = segSize
                  , segLb = startNum
                  , segUb = segUb
                  , casesForTest = L.reverse casesForTest2
                  , lbForTest = lb2
                  , ubForTest = ub2
                  , casesAreDense = isDense2
                  , casesForTestSize = segSize2
                  , otherLabel = calcOtherLabel lab1InfoOpt
                  }, [])
            | otherwise -> Nothing
    go xs@(p@(n, lab) : restIntLabel) segSize segUb lab1InfoOpt lab2InfoOpt
      = if | Just p1@(lab1, _, _, _, _, _) <- lab1InfoOpt
             , Just p2@(lab2, _, _, _, _, _) <- lab2InfoOpt
           -> if lab /= lab1 && lab /= lab2      -- cannot continue.  Just pick one and return
             then (pickOne lab1InfoOpt lab2InfoOpt, xs)
             else if lab == lab1
             then extendOneAndContinueIfPossible p1 p restIntLabel
             else extendOneAndContinueIfPossible p2 p restIntLabel
           | Just (p1@(lab1, _, _, _, _, _)) <- lab1InfoOpt
           , Nothing <- lab2InfoOpt
           -> if lab /= lab1 && (Maybe.isNothing defOpt || lab == Maybe.fromJust defOpt)
              then undefined -- we can continue... add it as second arg and recurse
              else undefined-- we are done.  see if we can use p1
           | Nothing <- lab1InfoOpt
             , Nothing <- lab1InfoOpt
           -> undefined -- Add it as the first and go from here.
           | Nothing <- lab1InfoOpt
             , Just (_, _, _, _, _, _) <- lab2InfoOpt
           -> U.impossible ()
             
             
             {-
    go :: [IntLabel] -> S.Set Label -> Int -> Integer -> Bool -> [IntLabel]
          -> Maybe (SegmentType, [IntLabel])
    go [] _ segSize segUb isDense casesForTest
      = if segSize < minBitTestSize
        then Nothing
        else Just (TwoLabelsType1 {
            segSize = segSize
          , segLb = startNum
          , segUb = segUb
          , casesAreDense = isDense
          , casesForTest = reverse casesForTest
          , otherLabel = otherLabel
        }, [])

          startIntOpt = M.lookup lab m
          m' = M.insertWith (++) lab [n] m
          siz = M.size m'
        in
          if siz <= 2
          then
            if Maybe.isJust startIntOpt
            then
              let
                span = n - Maybe.fromJust startIntOpt + 1
              in
                if span > bitsLimit
                then 
             goNoDefault restIntLabel m'
          else (m, restIntLabel)

    goWithDefault :: [IntLabel] -> Label -> M.Map Label [Integer]
                     -> (M.Map Label [Integer], [IntLabel])
    goWithDefault [] _ m = (m, [])
    goWithDefault ((n, lab) : restIntLabel) defLabel m
      = let
          m' = M.insertWith (++) lab [n] m
          siz = M.size m'
        in
          if siz < 2 || (siz == 2 && M.member defLabel m')
          then goWithDefault restIntLabel defLabel m'
          else (m, restIntLabel)

-}
lab1 = L 1

lab2 = L 2

lab3 = L 3

lab4 = L 4

lab5 = L 5

{-

getGenericBitTestSegment :: SegmentConstructor -> LabelSizePredicate -> Integer ->
                            [IntLabel] -> Maybe Label -> Maybe (SegmentTypeWithSize, [IntLabel])
getGenericBitTestSegment segConstr labelSizePred bitsInWord intLabelList defOpt =
  if segmentSize < minBitTestSize
    then Nothing
    else Just ((segmentSize, segment), restOfList)
  where
    startIntLabel@(startNum, startLabel) = head intLabelList

    labelSet = S.insert startLabel (maybe S.empty S.singleton defOpt)
    (segmentSize, segment, restOfList) =
      let
        (segSiz, seg, rest) = go (tail intLabelList) labelSet 0 []
      in
        (segSiz + 1, segConstr $ startIntLabel : reverse seg, rest)

    go :: [IntLabel] -> S.Set Label -> Int -> [IntLabel] -> (Int, [IntLabel], [IntLabel])
    go [] _ segSiz result = (segSiz, result, [])
    go xs@(p@(n, lab) : restIntLabel) labSet segSiz result =
      let
        totalSpan = n - startNum + 1
       in
         if totalSpan > bitsInWord
         then (segSiz, result, xs)
         else
           let
             labSet' = S.insert lab labSet
           in
             if labelSizePred $ S.size labSet'
             then go restIntLabel labSet' (segSiz + 1) (p : result)
             else (segSiz, result, xs)

getType1BitTestSegment :: Integer -> [IntLabel] -> Maybe Label -> Maybe (SegmentTypeWithSize, [IntLabel])
getType1BitTestSegment bitsInWord = getGenericBitTestSegment BitTestType1Segment (<= 2) bitsInWord

getType2BitTestSegment :: Integer -> [IntLabel] -> Maybe Label -> Maybe (SegmentTypeWithSize, [IntLabel])
getType2BitTestSegment bitsInWord = undefined

getType3BitTestSegment :: Integer -> [IntLabel] -> Maybe Label -> Maybe (SegmentTypeWithSize, [IntLabel])
getType3BitTestSegment bitsInWord = getGenericBitTestSegment BitTestType3Segment (<= 4) (bitsInWord `div` 2)

getMultiWayJumpSegment :: [IntLabel] -> Maybe (SegmentTypeWithSize, [IntLabel])
getMultiWayJumpSegment intLabelList =
  let startIntLabel@(startNum, _) = head intLabelList

      (segmentSiz, jumpTableIntLabels, restOfList) = let (segSiz, ls, rest) = go startNum (tail intLabelList) 0 [] in (segSiz + 1, startIntLabel : reverse ls, rest)
   in if segmentSiz < minJumpTableSize
        then Nothing
        else Just ((segmentSiz, MultiWayJumpSegment jumpTableIntLabels), restOfList)
  where
    go :: Integer -> [IntLabel] -> Int -> [IntLabel] -> (Int, [IntLabel], [IntLabel])
    go _ [] segSiz res = (segSiz, res, [])
    go previous ls@(p@(n, _) : restIntLabel) !segSiz res =
      if n - previous >= maxJumpTableHole
        then (segSiz, res, ls)
        else go n restIntLabel (segSiz + 1) (p : res)

type SegInfo = (SegmentTypeWithSize, [IntLabel])

findSegment :: Integer -> Maybe Label -> [IntLabel] -> SegInfo
findSegment bitsInWord defOpt intLabelList =
  {-
        trace "" $
        tr intLabelList $
        trace "" $
        tr bitTest1Opt $
        trace "" $
        tr bitTest2Opt $
        trace "" $
        tr bitTest3Opt $
        trace "" $
        tr muplyWayOpt $
        trace "" $
  -}
  if  | Just res <- fullCoverage bitTest1 -> res -- If any one of the schemes gives full coverage then pick it
      | Just res <- fullCoverage bitTest2 -> res -- with priority BitTest1, BitTest2, BitTest3, MultiWayJump
      | Just res <- fullCoverage bitTest3 -> res
      | Just res <- fullCoverage multiWayJump -> res
      | otherwise -> pickLargest bitTest1 bitTest2 bitTest3 multiWayJump defSeg

  where
    bitTest1 = getType1BitTestSegment bitsInWord intLabelList defOpt
    bitTest2 = getType2BitTestSegment bitsInWord intLabelList defOpt
    bitTest3 = getType3BitTestSegment bitsInWord intLabelList defOpt
    multiWayJump = getMultiWayJumpSegment intLabelList

    defSeg = ((1, IsolatedValuesSegment [head intLabelList]), tail intLabelList)

    fullCoverage :: Maybe SegInfo -> Maybe SegInfo
    fullCoverage res@(Just (_, [])) = res
    fullCoverage _ = Nothing

    maxSegment :: SegInfo -> SegInfo -> SegInfo
    maxSegment res1@((size1, _), _) res2@((size2, _), _)
      = if size1 >= size2 then res1 else res2

    pickLargest :: Maybe SegInfo -> Maybe SegInfo -> Maybe SegInfo -> Maybe SegInfo
                   -> SegInfo -> SegInfo
    pickLargest s1 s2 s3 s4 def
      = maxSegment (maxSegment seg1 seg2) (maxSegment seg3 seg4)
      where
        seg1 = Maybe.fromMaybe def s1
        seg2 = Maybe.fromMaybe def s2
        seg3 = Maybe.fromMaybe def s3
        seg4 = Maybe.fromMaybe def s4

splitIntoSegments :: Integer -> Maybe Label -> [IntLabel] -> [SegmentTypeWithSize]
splitIntoSegments bitsInWord defOpt = go
  where
    go :: [IntLabel] -> [SegmentTypeWithSize]
    go [] = []
    go ls =
      let (segmentWithSize, rest) = findSegment bitsInWord defOpt ls
       in segmentWithSize : go rest

findMiddleSegment :: Int -> [SegmentTypeWithSize] -> ([SegmentTypeWithSize], SegmentTypeWithSize, [SegmentTypeWithSize])
findMiddleSegment totalSize =
  go 0 []
  where
    halfSize = totalSize `div` 2

    go :: Int -> [SegmentTypeWithSize] -> [SegmentTypeWithSize] -> ([SegmentTypeWithSize], SegmentTypeWithSize, [SegmentTypeWithSize])
    go n pre (seg@(segSiz, _) : rest) =
      if newTotalSize >= halfSize
        then (pre, seg, rest)
        else go newTotalSize (seg : pre) rest
      where
        newTotalSize = n + segSiz
    go _ _ [] = U.impossible ()

-}

{-

createPlanForIsolatedSegment :: Maybe Label -> [IntLabel] -> SwitchPlan
createPlanForIsolatedSegment defOpt intLabelList =
  undefined
  where

createPlanFromSegment :: Maybe Label -> SegmentTypeWithSize -> SwitchPlan
createPlanFromSegment defOpt seg =
  undefined
  where
    go (IsolatedValuesSegment {}) =
      undefined
    go (BitTestType1Segment {}) =
      undefined
    go (BitTestType2Segment {}) =
      undefined
    go (MultiWayJumpSegment {}) =
      undefined

createPlanFromSegments :: Maybe Label -> [SegmentTypeWithSize] -> SwitchPlan
createPlanFromSegments defOpt intLabelList =
  undefined
  where
    numCases = countCases intLabelList

    (prefix, (maxSegmentSize, maxSegment), postfix) = findMiddleSegment numCases intLabelList

    countCases :: [SegmentTypeWithSize] -> Int
    countCases = L.foldl' (\acc (n, _) -> acc + n) 0

{-
    findMaxSegment :: [SegmentTypeWithSize] -> ([SegmentTypeWithSize], SegmentTypeWithSize, [SegmentTypeWithSize])
    findMaxSegment [] = error "Should never happen"
    findMaxSegment (seg : segs)
      = go segs [] ([], seg, segs)
      where
        go :: [SegmentTypeWithSize] -> [SegmentTypeWithSize] -> ([SegmentTypeWithSize], SegmentTypeWithSize, [SegmentTypeWithSize])
              -> ([SegmentTypeWithSize], SegmentTypeWithSize, [SegmentTypeWithSize])
        go [] _ (pre, seg, post) = (reverse pre, seg, post)
        go (segment@(currentSize, _) : segments) pre maxSoFar@(_, (maxSizeSoFar, _), _)
          = go segments (segment : pre) (if currentSize > maxSizeSoFar then (pre, segment, segments) else maxSoFar)
-}
createPlan' :: Integer -> SwitchTargets -> Platform -> SwitchPlan
createPlan' bitsInWord st platform =
  undefined
  where
    defOpt :: Maybe Label
    defOpt = Nothing

    mkPlan :: [SegmentType] -> SwitchPlan
    mkPlan segmentList = undefined

    segmentToPlan :: SegmentType -> SwitchPlan
    segmentToPlan segmentType = undefined


cs0 :: [(Integer, Label)]
cs0 = [(1, lab1), (2, lab2), (3, lab1), (30, lab2), (40, lab1), (64, lab2)]

cs1 :: [(Integer, Label)]
cs1 =
  [ (1, lab1),
    (2, lab2),
    (3, lab2),
    (4, lab1),
    (7, lab2),
    (31, lab1),
    (32, lab2),
    (33, lab1),
    (63, lab1),
    (64, lab2),
    (65, lab1)
  ]

cs2 :: [(Integer, Label)]
cs2 =
  [ (1, lab1),
    (2, lab2),
    (3, lab2),
    (4, lab1),
    (7, lab2),
    (31, lab3),
    (32, lab2),
    (33, lab1),
    (63, lab1),
    (64, lab2),
    (65, lab1)
  ]

cs3 :: [(Integer, Label)]
cs3 =
  [ (1, lab1),
    (2, lab2),
    (3, lab2),
    (4, lab1),
    (7, lab2),
    (15, lab3),
    (16, lab2),
    (17, lab1),
    (31, lab1),
    (32, lab2),
    (33, lab1)
  ]

cs4 :: [(Integer, Label)]
cs4 =
  [ (1, lab1),
    (2, lab2),
    (3, lab3),
    (4, lab4),
    (7, lab2),
    (11, lab3),
    (13, lab5),
    (14, lab1),
    (15, lab3),
    (16, lab5),
    (17, lab1),
    (21, lab1),
    (25, lab2),
    (29, lab1),
    (31, lab1),
    (32, lab2),
    (33, lab1)
  ]

cs5 :: [(Integer, Label)]
cs5 = [(1, lab1), (100, lab2), (200, lab3), (300, lab4)]

m :: M.Map Integer Label
m = M.fromList cs0

splitAtHoles :: Integer -> M.Map Integer a -> [M.Map Integer a]
splitAtHoles _ m | M.null m = []
splitAtHoles holeSize m = map (\range -> restrictMap range m) nonHoles
  where
    holes = filter (\(l, h) -> h - l > holeSize) $ zip (M.keys m) (tail (M.keys m))
    nonHoles = reassocTuples lo holes hi

    (lo, _) = M.findMin m
    (hi, _) = M.findMax m

restrictMap :: (Integer, Integer) -> M.Map Integer b -> M.Map Integer b
restrictMap (lo, hi) m = mid
  where
    (_, mid_hi) = M.split (lo -1) m
    (mid, _) = M.split (hi + 1) mid_hi

-- for example: reassocTuples a [(b,segSiz),(d,e)] f == [(a,b),(segSiz,d),(e,f)]
reassocTuples :: a -> [(a, a)] -> a -> [(a, a)]
reassocTuples initial [] last =
  [(initial, last)]
reassocTuples initial ((a, b) : tuples) last =
  (initial, a) : reassocTuples b tuples last

-}
