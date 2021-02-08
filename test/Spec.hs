{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE NamedFieldPuns #-}

import Test.QuickCheck
import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.Maybe as Maybe
import qualified Switch as SW
import qualified Eval as EV

import Debug.Trace

lb :: Int
lb = 0

ub :: Int
ub = 100

spanOfRegion :: Int
spanOfRegion = ub - lb + 1

coinFlip :: Gen Int
coinFlip = choose (0, 1)

genSize :: Gen Int
genSize = choose (1, spanOfRegion - 1)

genInt :: Gen Integer
genInt = choose (fromIntegral lb, fromIntegral ub)

generateRandomSets :: Gen (S.Set Integer, S.Set Integer)
generateRandomSets =
  do
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
      forAll generateRandomSets $
        \(s1, s0) ->
          let
            (st, planOpt) = buildPlan lb ub platform s0 s1
          in
            collect (Maybe.isJust planOpt) $
            Maybe.isJust planOpt ==> 
            let
              Just plan = planOpt
              noBitAtTop = containsBitTestNotAtTopLevel plan
            in
              tr ("\n" ++ show (getLabelToInts st)) $
              tr (show plan) $
              collect (isBitTest plan) $
              collect noBitAtTop $
              doTest lb ub platform st plan

label0 = SW.L 0
label1 = SW.L 1

buildPlan :: Int -> Int -> SW.Platform -> S.Set Integer -> S.Set Integer -> (SW.SwitchTargets, Maybe SW.SwitchPlan)
buildPlan lb ub platform s0 s1
  = (st, planOpt)
  where
    platform = SW.Platform SW.bytesInWordForPlatform
    ls = [(s, label0) | s <- S.toList s0] ++ [(s, label1) | s <- S.toList s1]
    st = SW.mkSwitchTargets True (fromIntegral lb, fromIntegral ub) Nothing (M.fromList ls)
    planOpt = SW.createPlan st platform

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
m = 100

main = quickCheckWith stdArgs { maxSuccess = m } prop_switch_plan_test
