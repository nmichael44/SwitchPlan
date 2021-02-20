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

instance Show BitTestInfo where
  show :: BitTestInfo -> String
  show BitTestInfo { offset, magicConstant, bitTestFailedPlan }
    = "BitTestInfo { offset = " ++ show offset
               ++ ", magicConst = " ++ U.convIntegerToBinary bitsInWordForPlatform magicConstant
               ++ ", bitTestFailedPlan = " ++ show bitTestFailedPlan ++ " }"

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
createPlan st platform
  = let
    -- We have to do this because one of the integer labels could be the same as the default label
    -- Thus we build a set to remove possible duplicates.
      labelSet = let s = M.keysSet (getLabelToInts st) in maybe s (`S.insert` s) (getDefLabel st)
      numLabels = S.size labelSet
    in
      trace ("NumLabels: " ++ show numLabels) $
      if | numLabels == 1, Just plan <- createOneValPlan labelSet
           -> trace "1!!!" plan
         | numLabels == 2, Just plan <- createTwoValPlan labelSet st platform
           -> trace "2!!!" plan
         | numLabels == 3, Just plan <- createThreeValPlan st platform
           -> trace "3!!!" plan
         | Just plan <- createGeneralBitTest labelSet st platform
           -> trace "4!!!" plan
         | Just plan <- createJumpTable st
           -> trace "5!!!" plan
         | otherwise
           -> trace "6!!!" $ createSplitPlan (getSigned st) (splitInterval st) platform

createSplitPlan :: Bool -> (SwitchTargets, Integer, SwitchTargets) -> Platform -> SwitchPlan
createSplitPlan signed (stLeft, n, stRight) platform
  = IfLT signed n (createPlan stLeft platform) (createPlan stRight platform)

createOneValPlan :: S.Set Label -> Maybe SwitchPlan
createOneValPlan labelSet
  = let
      label = case S.toList labelSet of { [l] -> l; _ -> error "Should never happen" }
    in
      Just $ Unconditionally label

createTwoValPlan :: S.Set Label -> SwitchTargets -> Platform -> Maybe SwitchPlan
createTwoValPlan labelSet st@(SwitchTargets _ _ defLabelOpt _ _) platform
  = let  -- Can never fail but let's silence the ghc warning.
      (label1, label2) = case S.toList labelSet of { [lab1, lab2] -> (lab1, lab2); _ -> error "The improssible happened" }
    in
      case defLabelOpt of 
        Just defLabel -> createTwoValPlanWithDefault st (if label1 == defLabel then label2 else label1) bitsInWord
        Nothing -> createBitTwoValPlanNoDefault st label1 label2 bitsInWord
  where
    bitsInWord = 8 * fromIntegral (platformWordSizeInBytes platform)

-- Function creates a plan 
createBitTwoValPlanNoDefault :: SwitchTargets -> Label -> Label -> Integer -> Maybe SwitchPlan
createBitTwoValPlanNoDefault
  (SwitchTargets signed range@(lb, ub) _defLabelOpt _intToLabel labelToInts)
  label1
  label2
  bitsInWord
  = let
      label1Ints = case M.lookup label1 labelToInts of { Just ns -> ns; Nothing -> error "The improssible happened" }
      label2Ints = case M.lookup label2 labelToInts of { Just ns -> ns; Nothing -> error "The improssible happened" }

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

      intsGoingToDefaultLabel = Maybe.fromMaybe [] (M.lookup defLabel labelToInts)
      intToLabel' = L.foldl' (flip M.delete) intToLabel intsGoingToDefaultLabel
      labelToInts' = M.delete defLabel labelToInts

      --spanForDefault = U.computeSpan range intToLabel'
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
          labelInts = case M.lookup label labelToInts' of { Just ns -> ns; Nothing -> error "The impossible happened!" }
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

newtype T = T (Maybe (Label, [Integer], Bool, Bool))
  deriving Show

costOfT :: T -> Int
costOfT (T Nothing) = 100
costOfT (T (Just (_, ns, eqLb, eqUb)))
  = (2 - length ns) + (1 - U.ind eqLb) + (1 - U.ind eqUb) -- This 2 comes from the fact that only lists of 1 and 2
                                                          -- are allowed as candidates in createThreeValPlan() below.

createThreeValPlan :: SwitchTargets -> Platform -> Maybe SwitchPlan
createThreeValPlan
  (SwitchTargets signed (lb, ub) defLabelOpt intToLabel labelToInts)
  platform
  = let
      ls = M.toList $
             case defLabelOpt of
               Just defLabel -> M.delete defLabel labelToInts
               Nothing -> labelToInts
    in
      U.firstSuccess $ map tryLabel ls
  where
    tryLabel :: (Label, [Integer]) -> Maybe SwitchPlan
    tryLabel (lab, labelInts)
      = case labelInts of
          [n] | n == lb || n == ub
            -> let
                 intToLabel' = M.delete n intToLabel
                 labelToInts' = M.delete lab labelToInts
                 range' = if n == lb then (lb + 1, ub) else (lb, ub - 1)
                 st' = SwitchTargets signed range' defLabelOpt intToLabel' labelToInts'
                 elsePlan = createPlan st' platform
               in Just $ createEqPlanWithPlan labelInts lab elsePlan
          _ -> Nothing

pNumerator :: Int
pNumerator = 1

pDenominator :: Int
pDenominator = 2

-- We must have at least 4 cases going to the same label to apply the
-- BitTest optimization.  Any less than 4 and it's not worth it.
minNumberOfBitTestCases :: Int
minNumberOfBitTestCases = 4

createGeneralBitTest :: S.Set Label -> SwitchTargets -> Platform -> Maybe SwitchPlan
createGeneralBitTest
  _labelSet
  _st@(SwitchTargets _signed _range@(_lb, _ub) _defLabelOpt _intToLabel _labelToInts)
  _platform
 = Nothing
{-
    if q >= minNumberOfBitTestCases
     && q * pDenominator >= m * pNumerator
     && (spanFitsInAWord || rangeIsDense)
   then Just $ createBitTestPlan ()
   else Nothing
  where
    (maxLabel, sortedCases) = U.findPairWithMaxNumElems labelToInts
    q = length sortedCases
    m = M.size intToLabel

    regionRange@(regionLb, regionUb) = (head sortedCases, last sortedCases)
    regionSpan = regionUb - regionLb + 1

    spanFitsInAWord = regionSpan <= bitsInWord
    rangeIsDense = regionSpan == fromIntegral q

    bitsInWord = 8 * fromIntegral (platformWordSizeInBytes platform)

    createBitTestPlan :: () -> SwitchPlan
    createBitTestPlan ()
      = createBracketPlan signed leftFPlan rightFPlan bitTestPlan regionRange
      where
        doLeftBoundsCheck  = lb < regionLb
        doRightBoundsCheck = ub > regionUb

        leftFPlan = if doLeftBoundsCheck then Just (constructLeftFPlan ()) else Nothing
        rightFPlan = if doRightBoundsCheck then Just (constructRightFPlan ()) else Nothing

        bitTestPlan = undefined

    constructLeftFPlan () = createPlanAux (updateSwitchTargets st Nothing (Just (lb - 1)) []) defLabelOpt platform

    constructRightFPlan () = createPlanAux (updateSwitchTargets st (Just (ub + 1)) Nothing []) defLabelOpt platform

createPlanAux :: SwitchTargets -> Maybe Label -> Platform -> SwitchPlan
createPlanAux st@(SwitchTargets _ _ _ m _) mbdef platform
  = if M.null m then
      case mbdef of
        Just label -> Unconditionally label
        Nothing -> error "Something went horribly wrong..."
    else createPlan st platform

updateSwitchTargets :: SwitchTargets -> Maybe Integer -> Maybe Integer -> [Integer] -> SwitchTargets
updateSwitchTargets (SwitchTargets signed (lb, ub) label intToLabel _labelToInts) newLb newUb casesForRemoval
  = SwitchTargets signed (newLb', newUb') label intToLabel' labelToInts'
  where
    (newLb', m') = case newLb of
                     Just lb' -> (lb', snd (U.splitMap (lb' - 1) intToLabel))
                     Nothing -> (lb, intToLabel)
    (newUb', m'') = case newUb of
                      Just ub' -> (ub', fst (U.splitMap ub' m'))
                      Nothing -> (ub, m')

    intToLabel' = L.foldl' (flip M.delete) m'' casesForRemoval
    labelToInts' = U.calcRevMap intToLabel'
-}

maxJumpTableGapSize :: Integer
maxJumpTableGapSize = 6

minJumpTableSize :: Int
minJumpTableSize = 5

minJumpTableOffset :: Integer
minJumpTableOffset = 2

maxExpandSizeForDefaultForJumpTableOptimization :: Integer
maxExpandSizeForDefaultForJumpTableOptimization = 48

createJumpTable :: SwitchTargets -> Maybe SwitchPlan
createJumpTable st@(SwitchTargets _signed (lb, ub) defLabelOpt intToLabel _labelToInts)
  = case defLabelOpt of
      Just _ ->
        let
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
      Nothing -> createJumpTableAux st True

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
      existingIntsGointToDefault = Maybe.fromMaybe [] $ M.lookup defLabel labelToInts
      intToLabel' = L.foldl' (flip M.delete) intToLabel existingIntsGointToDefault
      labelToInts' = M.delete defLabel labelToInts

      numCasesForDefault = [(i, defLabel) | i <- [regLb..regUb], not (i `M.member` intToLabel')]

      intToLabel'' = L.foldl' (\m (i, l) -> M.insert i l m) intToLabel' numCasesForDefault
      labelToInts'' = M.insert defLabel (fst <$> numCasesForDefault) labelToInts'

      defl = if regLb == lb && regUb == ub then Nothing else defLabelOpt
    in
      SwitchTargets signed range defl intToLabel'' labelToInts''

expandRegion (SwitchTargets _ _ Nothing _ _) _ _ = error "The unthinkable happened!"

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
  = L.foldl' (\plan n -> IfEqual n thenLabel plan) elsePlan labelInts

createEqPlanFor3 :: Bool -> [Integer] -> Label -> Label -> (Integer, Integer) -> SwitchPlan
createEqPlanFor3 signed labelInts lab1 lab2 (lb, ub)
  = let
      (n0, n1, n2) = case labelInts of {[x0, x1, x2] -> (x0, x1, x2); _ -> error "The unthinkable happened!" }
    in
      if | n0 == lb && n0 + 1 == n1 -> IfLE signed n1 (Unconditionally lab1) (IfEqual n2 lab1 (Unconditionally lab2))
         | n2 == ub && n2 - 1 == n1 -> IfLT signed n1 (IfEqual n0 lab1 (Unconditionally lab2)) (Unconditionally lab1)
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
