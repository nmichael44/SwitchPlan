{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE NamedFieldPuns #-}

module UnitTests where

import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Maybe as Maybe
import qualified Data.Either as Either
import qualified Switch as SW
import qualified Eval as EV
import qualified Utils as U
import Control.Monad ( when, unless )
import Debug.Trace ( trace )

type Label = SW.Label 

data PieceOfCase
  = C Integer Label  -- usual case i.e. n -> L1
  | D Label          -- the default case

newtype DataTypeRange = DTR (Integer, Integer)
newtype TestingRange = TR (Integer, Integer)

data TestInputs = TI [PieceOfCase] DataTypeRange TestingRange SW.Platform
data TestCase = TC DataTypeRange TestingRange SW.SwitchTargets SW.Platform

mkTestCase :: Int -> TestInputs -> (Int, Either String TestCase)
mkTestCase testNum (TI cases dtr@(DTR (lb, ub)) tr@(TR (testLb, testUb)) platform)
  = (testNum,
     do
       intToLabel <- U.buildMap (cases >>= \case { (C i l) -> [(i, l)]; _ -> [] })
       let fullSet = S.fromAscList [lb..ub]
           numCases = M.size intToLabel

           defaults = cases >>= \case { (D l)-> [l]; _ -> [] }
           numDefaults = length defaults
       when (lb > ub) $ Left "Bad data type range."
       when (testLb > testUb) $ Left "Bad test range."
       when (testLb < lb || testUb > ub) $ Left "Bad test range with respect to datatype range."
       when (numCases == 0) $ Left "No cases specified."
       when (numDefaults > 1) $ Left "Too many defaults."
       when (numCases == 1 && numDefaults == 0 && ub - lb /= 0) $ Left "Missing default case."
       unless (S.isSubsetOf (M.keysSet intToLabel) (S.fromAscList [lb..ub])) $ Left "Cases outside of datatype range."
       when (S.difference fullSet (M.keysSet intToLabel) /= S.empty && numDefaults /= 1) $ Left "Missing cases but no default specified."
       when (fullSet == M.keysSet intToLabel && numDefaults == 1) $ Left "Default specified when no gaps."

       let
         defLabelOpt = if numDefaults == 0 then Nothing else Just $ head defaults
         st = SW.mkSwitchTargets True (lb, ub) defLabelOpt intToLabel

       return $ TC dtr tr st platform)

sShowPlans :: Bool
sShowPlans = True

doTest :: (Int, Either String TestCase) -> IO Bool
doTest (testNum, Right (TC (DTR (lb, ub)) (TR (testLb, testUb)) st@(SW.SwitchTargets _ _ defLabelOpt intToLabel _) platform))
  = do
      (if sShowPlans then putStrLn else putStr) $ "Test " ++ show testNum ++ ":"
      when sShowPlans (putStrLn $ "intToLabel: " ++ show intToLabel)
      when sShowPlans (putStrLn $ "DefaultLabel: " ++ show defLabelOpt)
      when sShowPlans (putStrLn $ "Range: " ++ show (lb, ub))
      when sShowPlans (putStrLn $ "Plan: " ++ show plan)
      let res = Maybe.catMaybes $ processRes <$> diffs
      if null res then do { putStrLn "Ok!\n"; return True } else do { putStrLn ""; mapM_ putStrLn res; return False }
  where
    plan = SW.createPlan st platform
    eval = EV.eval platform plan
    diffs = [(n, expected, res) | n <- [testLb..testUb],
             let expected = lookup n intToLabel defLabelOpt,
             let res = eval n]

    processRes :: (Integer, Label, Either String Label) -> Maybe String
    processRes (n, expectedLabel, Left errStr) = Just $ "For n: " ++ show n ++ " expected: " ++ show expectedLabel ++ " but instead got an error: \"" ++ errStr ++ "\""
    processRes (n, expectedLabel, Right resultLabel) = if expectedLabel /= resultLabel then Just $ "For n: " ++ show n ++ " expected: " ++ show expectedLabel ++ " but instead got: "  ++ show resultLabel else Nothing

    lookup :: Integer -> M.Map Integer Label -> Maybe Label -> Label
    lookup n m (Just defLabel) = Maybe.fromMaybe defLabel $ M.lookup n m
    lookup n m Nothing = case M.lookup n m of { Just ans -> ans; Nothing -> error "The unthinkable happened!" }

doTest (testNum, Left err) 
  = do { putStrLn $ "Test " ++ show testNum ++ ":\nInvalid input for test.  Error was: \"" ++ err ++ "\""; return False }

lab0, lab1, lab2, lab3 :: SW.Label
lab0 = SW.L 0
lab1 = SW.L 1
lab2 = SW.L 2
lab3 = SW.L 3

sPlatform :: SW.Platform
sPlatform = SW.Platform 1

type STC = (Int, Either String TestCase) -- Switch Test Case

test0_numVals_1_nd = mkTestCase 0 (TI [C 0 lab0] (DTR (0, 0)) (TR (0, 0)) sPlatform)
test1_numVals_1_nd = mkTestCase 1 (TI [C 0 lab0, C 1 lab0] (DTR (0, 1)) (TR (0, 1)) sPlatform)
test2_numVals_1_nd = mkTestCase 2 (TI [C 0 lab0, C 1 lab0, C 2 lab0] (DTR (0, 2)) (TR (0, 2)) sPlatform)

test3_numVals_1_wd = mkTestCase 3 (TI [C 0 lab0, D lab0] (DTR (0, 1)) (TR (0, 1)) sPlatform)
test4_numVals_1_wd = mkTestCase 4 (TI [C 0 lab0, C 1 lab0, D lab0] (DTR (0, 5)) (TR (0, 5)) sPlatform)
test5_numVals_1_wd = mkTestCase 5 (TI [C 1 lab0, C 2 lab0, C 3 lab0, D lab0] (DTR (0, 10)) (TR (0, 10)) sPlatform)

test6_numVals_2_nd = mkTestCase 6 (TI [C 1 lab0, C 2 lab1] (DTR (1, 2)) (TR (1, 2)) sPlatform)
test7_numVals_2_nd = mkTestCase 7 (TI [C 1 lab0, C 2 lab1, C 3 lab1] (DTR (1, 3)) (TR (1, 3)) sPlatform)
test8_numVals_2_nd = mkTestCase 8 (TI [C 1 lab0, C 2 lab1, C 3 lab0] (DTR (1, 3)) (TR (1, 3)) sPlatform)

test9_numVals_2_nd = mkTestCase 9 (TI [C 1 lab0, C 2 lab1, C 3 lab0, C 4 lab1] (DTR (1, 4)) (TR (1, 4)) sPlatform)

test10_numVals_2_nd = mkTestCase 10 (TI [C 1 lab0, C 2 lab1, C 3 lab0, C 4 lab1, C 5 lab1
                                       , C 6 lab0, C 7 lab1, C 8 lab0] (DTR (1, 8)) (TR (1, 8)) sPlatform)
test11_numVals_2_nd = mkTestCase 11 (TI [C 1 lab0, C 2 lab1, C 3 lab0, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab1, C 9 lab1] (DTR (1, 9)) (TR (1, 9)) sPlatform)

test12_numVals_2_nd = mkTestCase 12 (TI [C 1 lab0, C 2 lab0, C 3 lab1, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab1, C 9 lab1] (DTR (1, 9)) (TR (1, 9)) sPlatform)

test13_numVals_2_nd = mkTestCase 13 (TI [C 1 lab0, C 2 lab0, C 3 lab1, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab1, C 9 lab0, C 10 lab1] (DTR (1, 10)) (TR (1, 10)) sPlatform)

test14_numVals_2_nd = mkTestCase 14 (TI [C 1 lab0, C 2 lab0, C 3 lab1, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab1, C 9 lab0, C 10 lab1] (DTR (1, 10)) (TR (1, 10)) sPlatform)

test15_numVals_2_nd = mkTestCase 15 (TI [C 1 lab1, C 2 lab0, C 3 lab1, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab1, C 9 lab1, C 10 lab0, C 11 lab0] (DTR (1, 11)) (TR (1, 11)) sPlatform)
test16_numVals_2_nd = mkTestCase 16 (TI [C 1 lab1, C 2 lab1, C 3 lab0, C 4 lab0, C 5 lab0
                                       , C 6 lab0, C 7 lab0, C 8 lab0, C 9 lab0, C 10 lab1, C 11 lab0] (DTR (1, 11)) (TR (1, 11)) sPlatform)
test17_numVals_2_nd = mkTestCase 17 (TI [C 1 lab1, C 2 lab0, C 3 lab1, C 4 lab0, C 5 lab0
                                       , C 6 lab0, C 7 lab0, C 8 lab0, C 9 lab0, C 10 lab1, C 11 lab0] (DTR (1, 11)) (TR (1, 11)) sPlatform)

test18_numVals_2_nd = mkTestCase 18 (TI [C 1 lab0, C 2 lab0, C 3 lab1, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab0, C 9 lab1, C 10 lab1, C 11 lab1] (DTR (1, 11)) (TR (1, 11)) sPlatform)

test19_numVals_2_nd = mkTestCase 19 (TI [C 1 lab0, C 2 lab1, C 3 lab0, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab0, C 9 lab0] (DTR (1, 9)) (TR (1, 9)) sPlatform)

allTests :: [STC]
allTests = [test0_numVals_1_nd, test1_numVals_1_nd, test2_numVals_1_nd
            , test3_numVals_1_wd, test4_numVals_1_wd, test5_numVals_1_wd
            , test6_numVals_2_nd, test7_numVals_2_nd, test8_numVals_2_nd
            , test9_numVals_2_nd, test10_numVals_2_nd, test11_numVals_2_nd
            , test12_numVals_2_nd, test13_numVals_2_nd, test14_numVals_2_nd
            , test15_numVals_2_nd, test16_numVals_2_nd
            , test17_numVals_2_nd, test18_numVals_2_nd, test19_numVals_2_nd]

executeAndReport :: [IO Bool] -> IO ()
executeAndReport actions
  = do
      results <- sequence actions
      let (numSuccesses, numFailures) = L.foldl' (\(s, f) e -> if e then (s + 1, f) else (s, f + 1)) (0, 0) results
      putStrLn ("\nResults:\nSuccesses: " ++ show numSuccesses ++ "\nFailures: " ++ show numFailures)

main :: IO ()
main =
  executeAndReport (doTest <$> allTests)
