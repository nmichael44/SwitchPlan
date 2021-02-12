{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE NamedFieldPuns #-}

import Test.QuickCheck
import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.Maybe as Maybe
import qualified Switch as SW
import qualified Eval as EV
import qualified Utils as U

import Debug.Trace

type Label = SW.Label 

data PieceOfCase
  = C (Integer, Label)  -- usual case i.e. n -> L1
    | D Label       -- the default case

newtype DataTypeRange = DTR (Integer, Integer)
newtype TestingRange = TR (Integer, Integer)

data TestCase = TestCase [PieceOfCase] DataTypeRange TestingRange SW.SwitchTargets SW.Platform

mkTestCase :: [PieceOfCase] -> DataTypeRange -> TestingRange -> SW.Platform -> TestCase
mkTestCase cases dtr@(DTR (lb, ub)) tr@(TR (testLb, testUb)) platform
  = let
      fullSet = S.fromAscList [lb..ub]
      intToLabel =
        case U.buildMap (cases >>=  (\case { (C p) -> [p]; (D _) -> [] })) of
          Left err -> error err
          Right m -> m
      numCases = M.size intToLabel

      defaults = concatMap (\case { (C _) -> []; (D l)-> [l] }) cases
      numDefaults = length defaults
    in
      if | lb > ub -> error "Bad data type range."
         | testLb > testUb -> error "Bad data type range."
         | numCases == 0 -> error "No cases specified."
         | numDefaults > 1 -> error "Too many defaults"
         | numCases == 1 && numDefaults == 0 -> error "Missing default case."
         | not $ S.isSubsetOf (M.keysSet intToLabel) (S.fromAscList [lb..ub]) -> error "Cases outside of datatype range."
         | S.difference fullSet (M.keysSet intToLabel) /= S.empty && numDefaults /= 1 -> error "Missing cases but no default specified."
         | fullSet == M.keysSet intToLabel && numDefaults == 1 -> error "Default specified when no gaps."
         | otherwise ->
           let
             defLabelOpt = if numDefaults == 0 then Nothing else Just $ head defaults
             st = SW.mkSwitchTargets True (lb, ub) defLabelOpt intToLabel
           in
             TestCase cases dtr tr st platform

lb :: Int
lb = 0

ub :: Int
ub = 6

spanOfRegion :: Int
spanOfRegion = ub - lb + 1

coinFlip :: Gen Int
coinFlip = choose (0, 1)

genSize :: Gen Int
genSize = choose (1, spanOfRegion - 1)

genInt :: Gen Integer
genInt = choose (fromIntegral lb, fromIntegral ub)

generateTwoRandomSets :: Gen (S.Set Integer, S.Set Integer)
generateTwoRandomSets =
  do
    size <- genSize
    let lsm = replicate size genInt
    ls <- sequence lsm
    let s0 = S.fromList ls
    let s1 = S.difference (S.fromAscList [(fromIntegral lb)..(fromIntegral ub)]) s0
    c <- coinFlip
    return (if c == 0 then (s0, s1) else (s1, s0))

generateRandomSets :: Int -> Gen (S.Set Integer, S.Set Integer)
generateRandomSets maxNumOfSets =
  do
    numSets <- choose (2, maxNumOfSets)
    size <- genSize
    let lsm = replicate size genInt
    ls <- sequence lsm
    let s0 = S.fromList ls
    let s1 = S.difference (S.fromAscList [(fromIntegral lb)..(fromIntegral ub)]) s0
    c <- coinFlip
    return (if c == 0 then (s0, s1) else (s1, s0))

isBitTest :: SW.SwitchPlan -> Bool
isBitTest (SW.BitTest _) = True
isBitTest _ = False

containsBitTestNotAtTopLevel :: SW.SwitchPlan -> Bool
containsBitTestNotAtTopLevel plan
  = case plan of
      (SW.BitTest SW.BTOI { SW.bitTestInfo = SW.BitTestInfo { SW.offset, SW.magicConstant, SW.bitTestFailedPlan }, SW.bitTestSucceededPlan }) -> go bitTestSucceededPlan || go bitTestFailedPlan
      pl -> go pl
  where
    go (SW.Unconditionally _) = False 
    go (SW.IfEqual _ _ falsePlan) = go falsePlan
    go (SW.IfLT _ _ thenPlan elsePlan) = go thenPlan || go elsePlan
    go (SW.IfLE _ _ thenPlan elsePlan) = go thenPlan || go elsePlan
    go (SW.BitTest _) = True
    go (SW.JumpTable _) = False

getLabelToInts :: SW.SwitchTargets -> M.Map SW.Label [Integer]
getLabelToInts (SW.SwitchTargets _ _ _ _ m _) = m

doTrace :: Bool
doTrace = False

tr :: String -> a -> a
tr str = if doTrace then trace str else id

prop_switch_plan_test :: Property
prop_switch_plan_test
  = let
      platform = SW.Platform SW.bytesInWordForPlatform
    in
      forAll generateTwoRandomSets $
        \(s1, s0) ->
          let
            (st, plan) = buildPlan lb ub platform s0 s1
            noBitAtTop = containsBitTestNotAtTopLevel plan
          in
            tr ("\n" ++ show (getLabelToInts st)) $
            tr (show plan) $
            collect (isBitTest plan) $
            collect noBitAtTop $
            doTest lb ub platform st plan

label0 = SW.L 0
label1 = SW.L 1

buildPlan :: Int -> Int -> SW.Platform -> S.Set Integer -> S.Set Integer -> (SW.SwitchTargets, SW.SwitchPlan)
buildPlan lb ub platform s0 s1
  = trace (show st) $
    trace (show plan) $
    (st, plan)
  where
    platform = SW.Platform SW.bytesInWordForPlatform
    ls = [(s, label0) | s <- S.toList s0] ++ [(s, label1) | s <- S.toList s1]
    st = SW.mkSwitchTargets True (fromIntegral lb, fromIntegral ub) Nothing (M.fromList ls)
    plan = SW.createPlan st platform

doTest :: Int -> Int -> SW.Platform -> SW.SwitchTargets -> SW.SwitchPlan -> Bool
doTest start end platform st plan
  = go start
  where
    (SW.SwitchTargets _ _ _ intToLabel labelToInts _) = st
    go start
      | start > end = True
      | otherwise =
        let
          start' = fromIntegral start
          res = EV.eval platform plan start'
          expectedRes = case M.lookup start' intToLabel of { Just lab -> lab; Nothing -> error "Unthinkable!" }
        in
          (if res /= expectedRes
          then trace ("\nstart: " ++ show start' ++ " res: " ++ show res ++ " expectedRes: " ++ show expectedRes ++ "\nplan: " ++ show plan ++ "\nintToLabel: " ++ show intToLabel ++ "\nlabelToInt: " ++ show labelToInts)
          else id)
          (res == expectedRes && go (start + 1))

m:: Int
m = 4

main = quickCheckWith stdArgs { maxSuccess = m } prop_switch_plan_test
