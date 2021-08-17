{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Switch where

import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Map.Lazy as M
import qualified Data.Maybe as Maybe
import qualified Data.Set as S
import qualified Data.Bifunctor as BiFunc

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
cbp signed doLeftCheck leftPlan doRightCheck rightPlan middlePlan (lb, ub) =
  createBracketPlan
    signed
    (if doLeftCheck then leftPlan else Nothing)
    (if doRightCheck then rightPlan else Nothing)
    middlePlan
    lb
    ub

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

{-
createBracketPlan :: Bool -> Maybe SwitchPlan -> Maybe SwitchPlan -> SwitchPlan
                     -> (Integer, Integer) -> SwitchPlan
createBracketPlan signed leftBracketPlanOpt rightBracketPlanOpt bitTestPlan (lb, ub) =
  case (leftBracketPlanOpt, rightBracketPlanOpt) of
    (Just leftPlan, Just rightPlan) -> IfLT signed lb leftPlan (IfLE signed ub bitTestPlan rightPlan)
    (Just leftPlan, Nothing) -> IfLT signed lb leftPlan bitTestPlan
    (Nothing, Just rightPlan) -> IfLE signed ub bitTestPlan rightPlan
    (Nothing, Nothing) -> bitTestPlan
-}

-------------------------------------------------------------

tr :: Show a => a -> b -> b
tr obj = trace (show obj)

type IntLabel = (Integer, Label)

{-
Let span = nk - n1 + 1.
    spanL1 = lastNOfL1 - firstNOfL1 + 1
    spanL2 = lastNOfL2 - firstNOfL2 + 1

Let exp be the input expression of the switch.

Two or Three Labels Contiguous regions:
=======================================
These are case expressions of the form:

ni -> L1
ni + 1 -> L1
ni + 2 -> L1
...
ni + ki -> L1
(potential gap)
nj     -> L2
nj + 1 -> L2
nj + 2 -> L2
...
nj + kj -> L2
(potential gap)
nm     -> L3
nm + 1 -> L3
nm + 2 -> L3
...
nm + kk -> L3
_       -> L4

with or without default.  The default label is allowed to be any
of the existing labels.
The third region is allowed to not be there.

Assuming ni <= exp <= nm + kk, this is compiled into:

    if (exp <= ni + ki)
      goto L1;
    else if (nj <= exp && exp <= nj + kj)
      goto L2;
    else if (nm <= exp)
      goto L3; 
    else
      goto L4;

If we only have two regions (there is not L3 label and the
default is still L4) under the assumption that ni <= exp <= nj + kj
this gets compiled into:

    if (exp <= ni + ki)
      goto L1;
    else if (nj <= exp)
      goto L2;
    else
      goto L4;

For just one region then it's simply a goto L1 (under the assumption
ni <= exp <= ni + ki).

Another optimization we do is not to issue some of the comparisons
if the regions are consecutive.

Two Labels Type 1:
==================
An interval with exactly two labels and no default label of the form:

n1 -> L1
n2 -> L2
n3 -> L1
...
nk -> L2

or with default that is the same as one of the existing cases of the form:

n1 -> L1
n2 -> L2
n3 -> L1
...
nk -> L2
_  -> L1

and with span <= bitsInWord.

Assuming n1 <= exp <= nk, this is compiled into:

  1. if ((magicContantForL2 << exp) < 0)
       goto L2;
     else
       goto L1;

  or

  2. if ((magicConstantForL2 << (exp - n1)) < 0)
       goto L2;
     else
       goto L1;

depending on the values of n1, nk.

Two Labels Type 2:
==================
An interval with exactly two labels and no default label of the form:

n1 -> L1
n2 -> L2
n3 -> L1
...
nk -> L2

or with default that is the same as one of the existing cases of the form:

n1 -> L1
n2 -> L2
n3 -> L1
...
nk -> L2
_  -> L1

and with spanL1 <= bitsInWord OR spanL2 <= bitsInWord for the first example,
and spanL2 <= bitsInWord for the second example (since L1 is the default label).

Assuming n1 <= exp <= nk, and assuming spanL2 <= bitsInWord this is compiled into:

  1. if (firstNOfL2 <= exp && exp <= lastNOfL2 && (magicContantForL2 << (exp - firstNOfL2)) < 0)
       goto L2;
     else
       goto L1;

  Note (***): We note here that if n1 == firstNOfL2 then the first comparison will not be emited
  and likewise for e <= lastNOfL2.  Also there is room for an improvement in the computation of
  (magicContantForL2 << (exp - firstNOfL2)) -- depending on the values of firstNOfL2 and lastNOfL2
  we can avoid the subtraction (by building (at compile time) a different magic constant).

Three Labels:
=============
An interval with exactly three labels and no default label of the form:

n1 -> L1
n2 -> L2
n3 -> L3
n4 -> L3
...
nk -> L2

or with default that is the same as one of the existing cases of the form:

n1 -> L1
n2 -> L2
n3 -> L3
n4 -> L2
...
nk -> L3
_  -> L2

and with two of (spanL1 <= bitsInWord, spanL2 <= bitsInWord , spanL2 <= bitsInWord)
being true (for the first example), and spanL1 <= bitsInWord spanL3 <= bitsInWord (for the
second example since L2 is the default label).

Assuming n1 <= exp <= nk, and assuming spanL1 <= bitsInWord, spanL3 <= bitsInWord
this is compiled into:

  1. if (firstNOfL1 <= e && e <= lastNOfL1 && (magicContantForL1 << (exp - firstNOfL1)) < 0)
       goto L1;
     else if (firstNOfL3 <= e && e <= lastNOfL3 && (magicContantForL3 << (exp - firstNOfL3)) < 0)
       goto L3;
     else
       goto L2;

  Also see note (***) above which is also appicable here.

  We don't currently implement this one (because it's probably not worth it -- see below).

Three/Four Labels:
==================
An interval with exactly three, or four (counting a possible default label) and with span <= bitsInWord / 2.
For example (for 4 labels):

(no default)
n1 -> L1
n2 -> L2
n3 -> L3
n4 -> L3
...
nk -> L4

(with default)
n1 -> L1
n2 -> L2
n3 -> L3
n4 -> L3
...
nk -> L4
_  -> L3

The idea here is that we will use 2 bits to encode the presense of a label so we can distinguish up to four labels.

Assuming n1 <= exp <= nk, this is compiled into:

    1. (no default)
    
    int e = exp - n1;
    int c = (magicConstant >> (e + e)) && 0b11;

    if (c == 0b01)
      goto L1;
    else if (c == 0b10)
      goto L2;
    else if (c == 0b11)
      goto L3;
    else
      goto L4;

    Another optimization we do here is that we rearrange the order of the labels so that the ones that get checked earlier
    are those with the most cases.  So here L1 would be the one with the most cases going to it, L2 the second largest etc.

    2. (with default)

    int e = exp - n1;
    int c = (magicConstant >> (e + e)) && 0b11;

    if (c == 0b01)
      goto L1;
    else if (c == 0b10)
      goto L2;
    else if (c == 0b11)
      goto L4;
    else
      goto L3;

  Notes: The 3 label case overlaps the (Three Label) compilation scheme above.  They do have different constraints though
  (this scheme uses 2 bits per label) so there are cases when this one is not applicable but the other one is.
  When they are both applicable I believe this one is faster.  We only implement this one.  I dp not believe it is worth
  the trouble of doing both.
-}

data ContiguousSegment
  = ContiguousSegment {
      cSegLabel :: Label
    , cSegLb :: Integer
    , cSegUb :: Integer
    , cSegCases :: [IntLabel]}
  deriving Eq

instance Show ContiguousSegment where
  show ContiguousSegment {cSegLabel, cSegLb, cSegUb, cSegCases }
    = "CSeg ["
      ++ "Label: " ++ show cSegLabel
      ++ ", Lb: " ++ show cSegLb
      ++ ", Ub: " ++ show cSegUb
      ++ ", Cases: " ++ show cSegCases ++ "]"

data SegmentType
  = IsolatedValues {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , casesAreDense :: Bool
    , cases :: [IntLabel]
    }
  |  SimpleRegion { -- It doesn't matter what the input expression is.  Always go to `label`.
      label :: Label
    , segLb :: Integer
    , segUb :: Integer
    }
  | ContiguousRegions {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , numberOfSegments :: Int
    , contiguousSegments :: [ContiguousSegment]
    , defLabel :: Maybe Label
  }
  | TwoLabelsType1 {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , labelForCases :: Label
    , casesForTest :: [IntLabel] -- FIX THIS! via GotoLabel! Not true: This can be empty.  That means we have something like : (1 -> L1, 2 -> L1, _ -> L1) i.e. everything going to default.
    , otherLabel :: Label
    }
  | TwoLabelsType2 {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , labelForCases :: Label
    , casesForTest :: [IntLabel]
    , casesForTestSize :: Int
    , lbForTest :: Integer
    , ubForTest :: Integer
    , otherLabel :: Label
    }
  | FourLabels {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , fourLabelCases :: [[IntLabel]]
    , fourLabelOtherLabel :: Maybe Label
    }
  | MultiWayJump {
      segSize :: Int
    , segLb :: Integer
    , segUb :: Integer
    , cases :: [IntLabel]
    , multiWayJumpOtherLabel :: Maybe Label
    }
  deriving (Show, Eq)

printSeg :: SegmentType -> IO ()
printSeg seg
  = putStrLn ("\n" ++ show seg)

printSegs :: [SegmentType] -> IO ()
printSegs segs = F.forM_ segs printSeg

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
  = L.foldr mergeSegments []  -- foldr here to avoid the O(n^2) cost with the append of the 'cases' lists.
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

maxNumberOfLabelContiguousRegions :: Int
maxNumberOfLabelContiguousRegions = 3

getContiguousSegment :: [IntLabel]
                     -> Maybe Label
                     -> Maybe (SegmentType, [IntLabel])
getContiguousSegment intLabelList defOpt
  = let
      (totalSegSize, numberOfSegments, segments, rest) = splitIntoContSegments intLabelList 0 0 []
      (numberOfSegments', nonDefaultSegments)
        = Maybe.maybe (numberOfSegments, segments) (removeDefaultLabelIfPresent segments numberOfSegments) defOpt
      contiguousSegments = L.map createSegment nonDefaultSegments
    in
      Just (
        ContiguousRegions {
          segSize = totalSegSize
        , segLb = cSegLb . L.head $ contiguousSegments
        , segUb = cSegUb . L.last $ contiguousSegments
        , numberOfSegments = numberOfSegments'
        , contiguousSegments = contiguousSegments
        , defLabel = defOpt
        }
        , rest)
  where
    removeDefaultLabelIfPresent segments numSegments defLabel
      = BiFunc.second L.reverse $ go segments numSegments []
      where
        go [] numSegs res = (numSegs, res)
        go (p@(label, _) : rest) !numSegs res
          | label == defLabel = go rest (numSegs - 1) res
          | otherwise = go rest numSegs (p : res)

    splitIntoContSegments ::
        [IntLabel]               -- the input list
        -> Int                   -- total number of cases consumed (totalSegSize)
        -> Int                   -- number of cont segments
        -> [(Label, [IntLabel])] -- accumation variable
        -> (Int, Int, [(Label, [IntLabel])], [IntLabel])

    splitIntoContSegments [] totalSegSize numberOfSegments res
      = (totalSegSize, numberOfSegments, L.reverse res, [])

    splitIntoContSegments xs !totalSegSize numberOfSegments res
      | numberOfSegments >= maxNumberOfLabelContiguousRegions
        = (totalSegSize, numberOfSegments, L.reverse res, xs)
      | otherwise
        = let
            (label, piece, intLabs) = getLabelCases xs
            currSegSize = L.length piece
          in
            splitIntoContSegments
              intLabs
              (totalSegSize + currSegSize)
              (numberOfSegments + 1)
              ((label, piece) : res)

    getLabelCases :: [IntLabel] -> (Label, [IntLabel], [IntLabel])
    getLabelCases intLabs
      = go (L.tail intLabs) [firstCase]
      where
        firstCase = head intLabs
        label = snd firstCase

        go :: [IntLabel] -> [IntLabel] -> (Label, [IntLabel], [IntLabel])
        go [] res = (label, res, [])
        go bs@(q@(y, ylab) : rest) res@((z, zlab) : _)
          | y == z + 1, ylab == zlab = go rest (q : res)
          | otherwise = (label, res, bs)
        go _ _ = U.impossible ()

    createSegment :: (Label, [IntLabel]) -> ContiguousSegment
    createSegment (label, segCases)
      = let
          orderedSegCases = L.reverse segCases
          segLb = fst . head $ orderedSegCases
          segUb = fst . head $ segCases
        in
          ContiguousSegment {
            cSegLabel = label
          , cSegLb = segLb
          , cSegUb = segUb
          , cSegCases = orderedSegCases
        }

getTwoLabelsType1Segment :: Integer
                         -> [IntLabel]
                         -> Maybe Label
                         -> Maybe (SegmentType, [IntLabel])
getTwoLabelsType1Segment bitsInWord intLabelList defOpt
  = go (tail intLabelList) labelSet 1 startNum [startIntLabel]
  where
    startIntLabel@(startNum, startLabel) = head intLabelList
    labelSet = S.insert startLabel (Maybe.maybe S.empty S.singleton defOpt)

    go :: [IntLabel]
          -> S.Set Label
          -> Int
          -> Integer
          -> [IntLabel]
          -> Maybe (SegmentType, [IntLabel])
    go [] _ segSize segUb allCases
      = mkSegment segSize segUb allCases []

    go xs@(p@(n, lab) : restIntLabel) labSet !segSize segUb allCases
      = let
          totalSpan = U.rangeSpan startNum n
          labSet' = S.insert lab labSet
        in
          if S.size labSet' > 2
            || totalSpan > bitsInWord -- Idea for later:
                                      -- Here we can potentially ignore n's that
                                      -- go to the default label if there is one.
                                      -- We leave this optimization for future work.
          then mkSegment segSize segUb allCases xs
          else
            let
              segSize' = segSize + 1
              segUb' = n
              allCases' = p : allCases
            in
              go restIntLabel
                 labSet'
                 segSize'
                 segUb'
                 allCases'

    pickLabelWithGreatestFrequency :: [IntLabel] -> Label
    pickLabelWithGreatestFrequency intLabels
      = let
          m :: M.Map Label Int
          m = L.foldr (\(_, lab) acc -> M.insertWith (+) lab 1 acc) M.empty intLabels
        in
          case M.toList m of
            [(lab, _)] -> lab
            [(lab1, cnt1), (lab2, cnt2)] | cnt1 >= cnt2 -> lab1
                                         | otherwise -> lab2
            _ -> U.impossible ()

    mkSegment :: Int
              -> Integer
              -> [IntLabel]
              -> [IntLabel]
              -> Maybe (SegmentType, [IntLabel])
    mkSegment segSize segUb allCases rest
      | segSize < minBitTestSize = Nothing
      | otherwise
        = let
            (casesForTest, otherLabel) =
              let
                otlb = case defOpt of
                         Nothing -> pickLabelWithGreatestFrequency allCases
                         Just defLabel -> defLabel
              in
                (L.filter ((/= otlb) . snd) allCases, otlb)
          in
            Just
              (case casesForTest of
                 [] -- The only way this can happen is when everything goes to the same label (including the default if there is one).
                   -> SimpleRegion { label = otherLabel, segLb = fst . L.head $ intLabelList, segUb = fst . L.last $ intLabelList }
                 _ -> createSegment segSize segUb casesForTest otherLabel
              , rest)

    createSegment :: Int -> Integer -> [IntLabel] -> Label -> SegmentType
    createSegment segSize segUb casesForTest otherLabel
      = TwoLabelsType1 {
          segSize = segSize
        , segLb = startNum
        , segUb = segUb
        , labelForCases = snd . head $ casesForTest
        , casesForTest = L.reverse casesForTest
        , otherLabel = otherLabel
        }

getTwoLabelsType2Segment :: Integer
                         -> [IntLabel]
                         -> Maybe Label
                         -> Maybe (SegmentType, [IntLabel])
getTwoLabelsType2Segment bitsInWord intLabelList defOpt
  = go restIntLabelList 1 0 firstN startingMap
  where
    (m0, saturationLimit)
      = Maybe.maybe (M.empty, 2) (\defLabel -> (M.singleton defLabel Nothing, 1)) defOpt

    (q@(firstN, firstLabel), restIntLabelList) = (L.head intLabelList, L.tail intLabelList)
    startingMap | Just firstLabel == defOpt = m0
                | otherwise = M.insert firstLabel (Just (firstN, False, [q])) m0

    go :: [IntLabel]
          -> Int
          -> Int
          -> Integer
          -> M.Map Label (Maybe (Integer, Bool, [IntLabel]))
          -> Maybe (SegmentType, [IntLabel])
    go [] segSize _ prevN m
      = (, []) <$> mkSegmentIfPossible segSize prevN m

    go xs@(p@(n, lab) : rest) !segSize !saturatedCount !prevN m
      = case M.lookup lab m of
          Nothing ->
            if M.size m < 2
            then go rest
                    (segSize + 1)
                    saturatedCount
                    n
                    (M.insert lab (Just (n, False, [p])) m)
            else
              (, xs) <$> mkSegmentIfPossible segSize prevN m

          Just Nothing ->  -- We found it but it was the same as the default label.
            go rest (segSize + 1) saturatedCount n m

          Just (Just (startNum, saturated, intLabs))
            | saturated
              -> go rest (segSize + 1) saturatedCount n m
            | U.rangeSpan startNum n <= bitsInWord
              -> go rest
                    (segSize + 1)
                    saturatedCount
                    n
                    (M.insert lab (Just (startNum, False, p : intLabs)) m)
            | saturatedCount + 1 == saturationLimit
              -> -- We now have a new saturated segment.  Check to see if we can continue.
                 -- If not let's try to make a segment and return it.
                 (, xs) <$> mkSegmentIfPossible segSize prevN m
            | otherwise -- This one now becomes saturated (we could't add (n, lab)).
                        -- We must continue though because we know the other segment
                        -- is not saturated.
              -> go rest
                    (segSize + 1)
                    (saturatedCount + 1)
                    n
                    (M.insert lab (Just (startNum, True, intLabs)) m)

    mkSegmentIfPossible :: Int
                           -> Integer
                           -> M.Map Label (Maybe (Integer, Bool, [IntLabel]))
                           -> Maybe SegmentType
    mkSegmentIfPossible segSize lastN m
      | segSize < minBitTestSize = Nothing
      | otherwise = Just $
          case M.toList m of
            -- Here label is default
            [(lab, Nothing)]
              -> SimpleRegion {
                  label = lab,
                  segLb = fst . head $ intLabelList,
                  segUb = fst . L.last $ intLabelList }

            -- There is no default in the segment and we only found one label -- so just go to it.
            [(lab, Just (startNum, _, intLabels))]
              -> SimpleRegion {
                   label = lab,
                   segLb = startNum,
                   segUb = fst . head $ intLabels }

            [(lab1, Nothing),
             (lab2, Just x2@(_, saturated2, _))]
               | saturated2 -> U.impossible ()
               | otherwise -> createSegment segSize lastN lab2 lab1 x2

            [(lab1, Just x1@(_, saturated1, _)),
             (lab2, Nothing)]
               | saturated1 -> U.impossible ()
               | otherwise -> createSegment segSize lastN lab1 lab2 x1

            [(lab1, Just x1@(startN1, saturated1, intLabels1)),
             (lab2, Just x2@(startN2, saturated2, intLabels2))]
               | saturated1 && saturated2 -> U.impossible ()
               | saturated1 -> createSegment segSize lastN lab2 lab1 x2
               | saturated2 -> createSegment segSize lastN lab1 lab2 x1
               | otherwise  ->
                 let
                   sp1 = U.rangeSpan startN1 (fst . head $ intLabels1)
                   sp2 = U.rangeSpan startN2 (fst . head $ intLabels2)
                in
                  if sp1 < sp2 -- Pick the one with the smallest span (for span = 1 or 2 we can compile it more efficiently).
                  then createSegment segSize lastN lab1 lab2 x1
                  else createSegment segSize lastN lab2 lab1 x2

            _ -> U.impossible ()

    createSegment :: Int -> Integer -> Label -> Label -> (Integer, Bool, [IntLabel]) -> SegmentType
    createSegment segSize lastN thisLabel otherLabel (startN, _, intLabels)
      = let
          segSize' = segSize
          segLb' = firstN
          segUb' = lastN
          labelForCases' = thisLabel
          (casesForTestSize', casesForTest') = U.revAndLen intLabels
          lbForTest' = startN
          ubForTest' = fst . head $ intLabels
          otherLabel' = otherLabel
        in
          TwoLabelsType2 {
            segSize = segSize'
          , segLb = segLb'
          , segUb = segUb'
          , labelForCases = labelForCases'
          , casesForTest = casesForTest'
          , casesForTestSize = casesForTestSize'
          , lbForTest = lbForTest'
          , ubForTest = ubForTest'
          , otherLabel = otherLabel'
        }

-- Idea for later:
-- In the presense of a default, if we have an interval with no gaps
-- in the integers then we can do Four labels without one of them having
-- to be equal to the default as this code requires.
-- We leave this for future work.

getFourLabelSegment :: Integer
                    -> [IntLabel]
                    -> Maybe Label
                    -> Maybe (SegmentType, [IntLabel])
getFourLabelSegment bitsInWord intLabelList defOpt
  = go (tail intLabelList) 1 startNum initialMap
  where
    bitsAvailable = bitsInWord `div` 2
    startIntLabel@(startNum, startLabel) = head intLabelList
    initialMap = M.insert startLabel
                          [startIntLabel]
                          (Maybe.maybe M.empty (`M.singleton` []) defOpt)

    mkSegment :: Int
              -> Integer
              -> M.Map Label [IntLabel]
              -> [IntLabel]
              -> Maybe (SegmentType, [IntLabel])
    mkSegment segSize segUb m rest
      | segSize < minBitTestSize = Nothing
      | otherwise
        = let
            m' = Maybe.maybe m (`M.delete` m) defOpt
            caseLists = L.map (L.reverse . snd) $ M.toList m'
          in
            Just
              (FourLabels {
                 segSize = segSize
               , segLb = startNum
               , segUb = segUb
               , fourLabelCases = caseLists
               , fourLabelOtherLabel = defOpt
               },
               rest)

    addToMap :: IntLabel -> Maybe [IntLabel] -> Maybe [IntLabel]
    addToMap p xs
      = Just $ h xs
      where h Nothing = [p]
            h (Just ys) = p : ys

    go :: [IntLabel]
       -> Int
       -> Integer
       -> M.Map Label [IntLabel]
       -> Maybe (SegmentType, [IntLabel])
    go [] segSize segUb m = mkSegment segSize segUb m []

    go xs@(p@(n, lab) : restIntLabel) !segSize segUb m
      = let
          totalSpan = U.rangeSpan startNum n
          m' = M.alter (addToMap p) lab m
        in
          if M.size m' > 4
            || totalSpan > bitsAvailable -- Idea for later:
                                         -- Here we can potentially ignore n's that
                                         -- go to the default label if there is one.
                                         -- We leave this optimization it for future work.
          then mkSegment segSize segUb m xs
          else
            let
              segSize' = segSize + 1
              segUb' = n
            in
              go restIntLabel segSize' segUb' m'

getMultiWayJumpSegment :: [IntLabel] -> Maybe Label -> Maybe (SegmentType, [IntLabel])
getMultiWayJumpSegment intLabelList defOpt =
  let
    startIntLabel@(startNum, _) = head intLabelList

    (segSize, segUb, ls, rest) = go startNum (tail intLabelList) 1 []
   in
     if segSize < minJumpTableSize
     then Nothing
     else
       Just (
         MultiWayJump {
           segSize = segSize
         , segLb = startNum
         , segUb = segUb
         , cases = startIntLabel : reverse ls
         , multiWayJumpOtherLabel = defOpt
         },
         rest)
  where
    go :: Integer
          -> [IntLabel]
          -> Int
          -> [IntLabel]
          -> (Int, Integer, [IntLabel], [IntLabel])
    go previous [] segSiz res = (segSiz, previous, res, [])

    go previous ls@(p@(n, _) : restIntLabel) !segSiz res
      | n - previous >= maxJumpTableHole = (segSiz, previous, res, ls)
      | otherwise = go n restIntLabel (segSiz + 1) (p : res)

findSegment :: Integer -> Maybe Label -> [IntLabel] -> (SegmentType, [IntLabel])
findSegment bitsInWord defOpt intLabelList =
{-
  trace "" $
  tr intLabelList $
  trace "" $
  tr contSeg $
  trace "" $
  tr btType1 $
  trace "" $
  tr btType2 $
  trace "" $
  tr btFourLabel $
  trace "" $
  tr multiWayJump $
  trace "" $
-}
  if  | Just res <- fullCoverage contSeg -> res -- If any one of the schemes gives full coverage then pick it
      | Just res <- fullCoverage btType1 -> res -- with priority ContiguousRegion, BitTest1, BitTest2, FourLabel, MultiWayJump
      | Just res <- fullCoverage btType2 -> res
      | Just res <- fullCoverage btFourLabel -> res
      | Just res <- fullCoverage multiWayJump -> res
      | otherwise -> pickLargest [contSeg, btType1, btType2, btFourLabel, multiWayJump]

  where
    contSeg = getContiguousSegment intLabelList defOpt
    btType1 = getTwoLabelsType1Segment bitsInWord intLabelList defOpt
    btType2 = getTwoLabelsType2Segment bitsInWord intLabelList defOpt
    btFourLabel = getFourLabelSegment bitsInWord intLabelList defOpt
    multiWayJump = getMultiWayJumpSegment intLabelList defOpt

    fullCoverage :: Maybe (SegmentType, [IntLabel]) -> Maybe (SegmentType, [IntLabel])
    fullCoverage res@(Just (_, [])) = res
    fullCoverage _ = Nothing

    maxSegment :: (SegmentType, [a]) -> (SegmentType, [a]) -> (SegmentType, [a])
    maxSegment seg0 seg1
      | (segSize . fst $ seg0) >= (segSize . fst $ seg1) = seg0
      | otherwise = seg1

    pickLargest :: [Maybe (SegmentType, [IntLabel])] -> (SegmentType, [IntLabel])
    pickLargest segments
      = largestSegment
      where
        validSegments = Maybe.catMaybes segments
        largestSegment = L.foldr1 maxSegment validSegments

splitIntoSegments :: [IntLabel] -> Integer -> Maybe Label -> [SegmentType]
splitIntoSegments intLabelList bitsInWord defOpt
  = go intLabelList
  where
    go :: [IntLabel] -> [SegmentType]
    go [] = []
    go ls =
      let
        (segmentWithSize, rest) = findSegment bitsInWord defOpt ls
      in
        segmentWithSize : go rest

splitSegments :: [SegmentType]
              -> Int
              -> ([SegmentType], Int, [SegmentType], Int)
splitSegments segments totalSize
  = (L.reverse leftSegmentRev, leftSegmentSize, rightSegment, rightSegmentSize)
  where
    halfSize = totalSize `div` 2

    (leftSegmentRev, leftSegmentSize, rightSegment, rightSegmentSize)
      = go 0 [] segments

    go :: Int
          -> [SegmentType]
          -> [SegmentType]
          -> ([SegmentType], Int, [SegmentType], Int)
    go accSize pre q@(seg : rest)
      | newTotalSize >= halfSize = (pre, accSize, q, totalSize - accSize)
      | otherwise = go newTotalSize (seg : pre) rest
      where
        segSize' = segSize seg
        newTotalSize = accSize + segSize'

    go _ _ [] = U.impossible ()

createBracketPlan :: Bool
                  -> Maybe SwitchPlan
                  -> Maybe SwitchPlan
                  -> SwitchPlan
                  -> Integer
                  -> Integer
                  -> SwitchPlan
createBracketPlan signed leftBracketPlanOpt rightBracketPlanOpt bitTestPlan lb ub =
  case (leftBracketPlanOpt, rightBracketPlanOpt) of
    (Just leftPlan, Just rightPlan) -> IfLT signed lb leftPlan (IfLE signed ub bitTestPlan rightPlan)
    (Just leftPlan, Nothing) -> IfLT signed lb leftPlan bitTestPlan
    (Nothing, Just rightPlan) -> IfLE signed ub bitTestPlan rightPlan
    (Nothing, Nothing) -> bitTestPlan

ccp regionLb regionUb intLabels bitsInWord signed defLabelOpt
 = createPlan' regionLb regionUb (splitIntoSegments intLabels bitsInWord defLabelOpt) signed defLabelOpt

createPlan' :: Integer -> Integer -> [SegmentType] -> Bool -> Maybe Label -> SwitchPlan
createPlan' regionLb regionUb allSegments signed defOpt
  = go allSegments globalTotalSize regionLb regionUb
  where
    globalTotalSize = L.foldl' (+) 0 $ L.map segSize allSegments

    go :: [SegmentType] -> Int -> Integer -> Integer -> SwitchPlan
    go [seg] _ lb ub = compileSegment seg lb ub defOpt
    go segments !totalSize !lb !ub
      = let
          (segmentsLeft, segmentLeftSize, segmentsRight, segmentRightSize)
            = splitSegments segments totalSize

          segment = head segmentsRight
          segmentLb = segLb segment

          planLeft = go segmentsLeft segmentLeftSize lb (segmentLb - 1)
          planRight = go segmentsRight segmentRightSize segmentLb ub
        in
          IfLT signed segmentLb planLeft planRight

    compileSimpleRegionSegment :: Label -> SwitchPlan
    compileSimpleRegionSegment = Unconditionally

    compileContinuousRegionsSegment :: Integer
                                    -> Integer
                                    -> Int
                                    -> Integer
                                    -> Integer
                                    -> Int
                                    -> [ContiguousSegment]
                                    -> Maybe Label
                                    -> SwitchPlan
    compileContinuousRegionsSegment currentLb currentUb segSize segLb segUb numberOfSegments contiguousSegments defLabelOpt
      = case (contiguousSegments, defLabelOpt) of
          -- We had a default label AND all cases present were going to it.
          -- This is the degenerate case but possible as a result of this algorithm; not possible directly from the user program.
          ([], Just defLabel) -> Unconditionally defLabel
          ([], Nothing) -> U.impossible ()

          (segs@(seg : _), Just defLabel)
             -> let
                  defLabelPlanOpt = Just . Unconditionally $ defLabel
                in
                  fst $
                  L.foldr (accum defLabelPlanOpt)
                          (Unconditionally defLabel, True)
                          ((currentLb - 1, seg) : L.zipWith (curry (BiFunc.first cSegUb)) segs (tail segs))

          (ContiguousSegment { cSegLabel = cSegLabel } : rest, Nothing)
            -> compileContinuousRegionsSegment currentLb currentUb segSize segLb segUb (numberOfSegments - 1) rest $ Just cSegLabel
      where
        accum :: Maybe SwitchPlan -> (Integer, ContiguousSegment) -> (SwitchPlan, Bool) -> (SwitchPlan, Bool)
        accum defLabelPlanOpt
              (segUb1,
               ContiguousSegment {
                 cSegLabel = cSegLabel2
               , cSegLb = cSegLb2
               , cSegUb = cSegUb2
               })
              (rightPlan, isGotoDefLabel)
          = let
              leftPlan2Opt | segUb1 + 1 /= cSegLb2 = defLabelPlanOpt
                           | otherwise = Nothing
              middlePlan2 = Unconditionally cSegLabel2
              rightPlan2Opt | cSegUb2 /= currentUb = Just rightPlan
                            | otherwise = Nothing -- This can only happen on the rightmost segment.
                                                  -- It's a shame we do the check for evert segment but it simplifies the code.

              segSpan = U.rangeSpan cSegLb2 cSegUb2

              -- If the span is 1, and the right plan was to go to default and the left plan is there (which means we are again going to default)
              -- then lets shortcircuit the usual thing and make a shorter plan based on equality instead of two comparisons.
              res | segSpan == 1 && isGotoDefLabel && Maybe.isJust leftPlan2Opt
                    = IfEqual cSegLb2 cSegLabel2 (Maybe.fromJust defLabelPlanOpt)
                  | otherwise
                    = createBracketPlan signed leftPlan2Opt rightPlan2Opt middlePlan2 cSegLb2 cSegUb2
            in
              (res, False)

    compileTwoLabelsType1Segment :: Integer
                                 -> Integer
                                 -> Int
                                 -> Integer
                                 -> Integer
                                 -> Label
                                 -> [IntLabel]
                                 -> Label
                                 -> SwitchPlan
    compileTwoLabelsType1Segment currentLb currentUb segSize segLb segUb labelForCases casesForTest otherLabel
      = undefined

    compileTwoLabelsType2Segment :: Integer
                                 -> Integer
                                 -> Int
                                 -> Integer
                                 -> Integer
                                 -> Label
                                 -> [IntLabel]
                                 -> Int
                                 -> Integer
                                 -> Integer
                                 -> Label
                                 -> SwitchPlan
    compileTwoLabelsType2Segment currentLb currentUb segSize segLb segUb labelForCases casesForTest casesForTestSize lbForTest ubForTest otherLabel
      = undefined

    compileFourLabelsSegment :: Integer
                             -> Integer
                             -> Int
                             -> Integer
                             -> Integer
                             -> [[IntLabel]]
                             -> Maybe Label
                             -> SwitchPlan
    compileFourLabelsSegment currentLb currentUb segSize segLb segUb fourLabelCases fourLabelOtherLabel
      = undefined

    compileMultiWayJumpSegment :: Integer
                               -> Integer
                               -> Int
                               -> Integer
                               -> Integer
                               -> [IntLabel]
                               -> Maybe Label
                               -> SwitchPlan
    compileMultiWayJumpSegment currentLb currentUb segSize segLb segUb cases multiWayJumpOtherLabel
      = undefined

    compileSegment :: SegmentType -> Integer -> Integer -> Maybe Label -> SwitchPlan
    compileSegment segment currentLb currentUb defOpt
      = go segment
      where
        go :: SegmentType -> SwitchPlan
        go SimpleRegion {
             label = label
           , segLb = _
           , segUb = _
           }
          = compileSimpleRegionSegment label

        go ContiguousRegions {
             segSize = segSize
           , segLb = segLb
           , segUb = segUb
           , numberOfSegments = numberOfSegments
           , contiguousSegments = contiguousSegments
           , defLabel = defLabel
           }
          = compileContinuousRegionsSegment currentLb currentUb segSize segLb segUb numberOfSegments contiguousSegments defLabel

        go TwoLabelsType1 {
             segSize = segSize
           , segLb = segLb
           , segUb = segUb
           , labelForCases = labelForCases
           , casesForTest = casesForTest
           , otherLabel = otherLabel
           }
          = compileTwoLabelsType1Segment currentLb currentUb segSize segLb segUb labelForCases casesForTest otherLabel

        go TwoLabelsType2 {
             segSize = segSize
           , segLb = segLb
           , segUb = segUb
           , labelForCases = labelForCases
           , casesForTest = casesForTest
           , casesForTestSize = casesForTestSize
           , lbForTest = lbForTest
           , ubForTest = ubForTest
           , otherLabel = otherLabel
           }
          = compileTwoLabelsType2Segment currentLb currentUb segSize segLb segUb labelForCases casesForTest casesForTestSize lbForTest ubForTest otherLabel

        go FourLabels {
             segSize = segSize
           , segLb = segLb
           , segUb = segUb
           , fourLabelCases = fourLabelCases
           , fourLabelOtherLabel = fourLabelOtherLabel
           }
          = compileFourLabelsSegment currentLb currentUb segSize segLb segUb fourLabelCases fourLabelOtherLabel

        go MultiWayJump {
             segSize = segSize
           , segLb = segLb
           , segUb = segUb
           , cases = cases
           , multiWayJumpOtherLabel = multiWayJumpOtherLabel
           }
          = compileMultiWayJumpSegment currentLb currentUb segSize segLb segUb cases multiWayJumpOtherLabel

        go _ = U.impossible ()
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
