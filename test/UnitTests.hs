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

lab0, lab1, lab2, lab3, lab4, lab5, lab6, lab7, lab8, lab9, lab10 :: SW.Label
lab0 = SW.L 0
lab1 = SW.L 1
lab2 = SW.L 2
lab3 = SW.L 3
lab4 = SW.L 4
lab5 = SW.L 5
lab6 = SW.L 6
lab7 = SW.L 7
lab8 = SW.L 8
lab9 = SW.L 9
lab10 = SW.L 10

sPlatform :: SW.Platform
sPlatform = SW.Platform 4

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

test20_numVals_2_nd = mkTestCase 20 (TI [C 1 lab0, C 2 lab1, C 3 lab0, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab0, C 9 lab0, C 10 lab1] (DTR (1, 10)) (TR (1, 10)) sPlatform)

test21_numVals_2_nd = mkTestCase 21 (TI [C 1 lab0, C 2 lab1, C 3 lab0, C 4 lab1, C 5 lab1
                                       , C 6 lab1, C 7 lab1, C 8 lab0, C 9 lab0, C 10 lab1, C 11 lab1] (DTR (1, 11)) (TR (1, 11)) sPlatform)

test22_numVals_2_nd = mkTestCase 22 (TI [C 0 lab0, C 1 lab0, C 100 lab1, C 200 lab2, D lab1] (DTR (0, 300)) (TR (0, 300)) sPlatform)
test23_numVals_2_nd = mkTestCase 23 (TI [C 0 lab0, C 2 lab1, C 10 lab1, C 299 lab2, C 300 lab2, D lab1] (DTR (0, 300)) (TR (0, 300)) sPlatform)
test24_numVals_2_nd = mkTestCase 24(TI [C 0 lab0, C 100 lab1, C 150 lab2, C 200 lab2, D lab1] (DTR (0, 300)) (TR (0, 300)) sPlatform)

test25_numVals_2_nd = mkTestCase 25 (TI [C 0 lab0, C 2 lab5, C 10 lab4, C 299 lab2, C 300 lab2, D lab1] (DTR (0, 300)) (TR (0, 300)) sPlatform)


test26_numVals_2_nd = mkTestCase 26 (TI [C 0 lab0, C 1 lab0, C 2 lab0, C 4 lab1, C 6 lab1, C 9 lab1, C 50 lab1, D lab2] (DTR (0, 51)) (TR (0, 50)) sPlatform)

test27_numVals_2_nd = mkTestCase 27 (TI [C 0 lab0, C 1 lab1, C 2 lab1, C 3 lab1, C 4 lab1] (DTR (0, 4)) (TR (0, 4)) sPlatform)
test28_numVals_2_nd = mkTestCase 28 (TI [C 0 lab0, C 1 lab0, C 2 lab1, C 3 lab1, C 4 lab1] (DTR (0, 4)) (TR (0, 4)) sPlatform)
test29_numVals_2_nd = mkTestCase 29 (TI [C 0 lab0, C 1 lab1, C 2 lab0, C 3 lab1, C 4 lab1] (DTR (0, 4)) (TR (0, 4)) sPlatform)
test30_numVals_2_nd = mkTestCase 30 (TI [C 0 lab0, C 1 lab0, C 2 lab0, C 3 lab0, C 23 lab0, C 44 lab0, C 60 lab0, C 61 lab0, D lab1] (DTR (0, 200)) (TR (0, 200)) sPlatform)
test31_numVals_2_nd = mkTestCase 31 (TI [C 0 lab0, C 1 lab0, C 2 lab0, C 3 lab0, C 23 lab0, C 44 lab0, C 60 lab0, C 61 lab0, C 63 lab0, D lab1] (DTR (0, 200)) (TR (0, 200)) sPlatform)
test32_numVals_2_nd = mkTestCase 32 (TI [C 0 lab0, C 1 lab0, C 2 lab0, C 3 lab0, C 23 lab0, C 44 lab0, C 60 lab0, C 61 lab0, C 64 lab0, D lab1] (DTR (0, 200)) (TR (0, 200)) sPlatform)
test33_numVals_2_nd = mkTestCase 33 (TI [C 0 lab0, C 10 lab1, C 11 lab0, C 13 lab0, C 14 lab0, C 17 lab0, C 60 lab0, C 61 lab0, C 64 lab0, D lab1] (DTR (0, 200)) (TR (0, 200)) sPlatform)
test34_numVals_2_nd = mkTestCase 34 (TI [C 0 lab0, C 100 lab1, C 199 lab3, C 200 lab0, C 300 lab0, C 400 lab0, C 700 lab0, C 800 lab0, D lab1] (DTR (0, 1000)) (TR (0, 1000)) sPlatform)
test35_numVals_2_nd = mkTestCase 35 (TI [C 1 lab0, C 2 lab0, C 3 lab2, C 4 lab2, C 5 lab0, C 6 lab1] (DTR (1, 6)) (TR (1, 6)) sPlatform)

test36_numVals_2_nd = mkTestCase 36 (TI [C 1 lab0, C 2 lab1, C 3 lab2, C 4 lab0, C 5 lab1,
                                         C 6 lab0, C 7 lab1, C 8 lab0, C 9 lab1,
                                         C 10 lab0, C 11 lab1, C 12 lab0, C 13 lab1] (DTR (1, 13)) (TR (1, 13)) sPlatform)

test37_numVals_2_nd = mkTestCase 37 (TI [C 1 lab0, C 2 lab0, C 3 lab1, C 4 lab0, C 5 lab1] (DTR (1, 5)) (TR (1, 5)) sPlatform)

test38_numVals_2_nd = mkTestCase 38 (TI [C 1 lab0, C 2 lab1, C 3 lab1, C 4 lab2, C 5 lab1, C 6 lab1] (DTR (1, 6)) (TR (1, 6)) sPlatform)
test39_numVals_2_nd = mkTestCase 39 (TI [C 1 lab1, C 2 lab0, C 3 lab1, C 4 lab2, C 5 lab1, C 6 lab1] (DTR (1, 6)) (TR (1, 6)) sPlatform)

test40_numVals_2_nd = mkTestCase 40 (TI [C 1 lab1, C 2 lab0, C 3 lab1, C 4 lab2, C 5 lab1, C 6 lab1] (DTR (1, 6)) (TR (1, 6)) sPlatform)

test41_numVals_2_nd = mkTestCase 41 (TI [C 1 lab1, C 2 lab0, C 3 lab0, C 4 lab2, C 5 lab1, C 6 lab1, D lab1] (DTR (1, 8)) (TR (1, 8)) sPlatform)

test42_numVals_2_nd = mkTestCase 42 (TI [C 1 lab0, C 2 lab0, C 3 lab0, C 4 lab0, C 5 lab0, C 6 lab0,
                                         C 7 lab0, C 8 lab1, C 9 lab1, C 10 lab0, C 11 lab1, C 12 lab1,
                                         C 13 lab0, C 14 lab1, C 15 lab2, C 16 lab0] (DTR (1, 16)) (TR (1, 16)) sPlatform)
test43_numVals_2_nd = mkTestCase 43 (TI [C 1 lab0, C 2 lab1, C 3 lab2, C 4 lab0, C 5 lab1, C 6 lab2,
                                         C 7 lab0, C 8 lab1, C 9 lab2, C 10 lab0, C 11 lab1, C 12 lab2,
                                         C 13 lab0, C 14 lab1, C 15 lab2, C 16 lab0, D lab1] (DTR (-1, 20)) (TR (-1, 20)) sPlatform)

allTests :: [STC]
allTests = [test0_numVals_1_nd, test1_numVals_1_nd, test2_numVals_1_nd
            , test3_numVals_1_wd, test4_numVals_1_wd, test5_numVals_1_wd
            , test6_numVals_2_nd, test7_numVals_2_nd, test8_numVals_2_nd
            , test9_numVals_2_nd, test10_numVals_2_nd, test11_numVals_2_nd
            , test12_numVals_2_nd, test13_numVals_2_nd, test14_numVals_2_nd
            , test15_numVals_2_nd, test16_numVals_2_nd
            , test17_numVals_2_nd, test18_numVals_2_nd, test19_numVals_2_nd
            , test20_numVals_2_nd, test21_numVals_2_nd
            , test22_numVals_2_nd, test23_numVals_2_nd, test24_numVals_2_nd
            , test25_numVals_2_nd
            , test26_numVals_2_nd
            , test27_numVals_2_nd
            , test28_numVals_2_nd
            , test29_numVals_2_nd
            , test30_numVals_2_nd
            , test31_numVals_2_nd
            , test32_numVals_2_nd
            , test33_numVals_2_nd
            , test34_numVals_2_nd
            , test35_numVals_2_nd
            , test36_numVals_2_nd
            , test37_numVals_2_nd
            , test38_numVals_2_nd
            , test39_numVals_2_nd
            , test40_numVals_2_nd
            , test41_numVals_2_nd
            , test42_numVals_2_nd
            , test43_numVals_2_nd
          ]

executeAndReport :: [IO Bool] -> IO ()
executeAndReport actions
  = do
      results <- sequence actions
      let (numSuccesses, numFailures) = L.foldl' (\(s, f) e -> if e then (s + 1, f) else (s, f + 1)) (0, 0) results
      putStrLn ("\nResults:\nSuccesses: " ++ show numSuccesses ++ "\nFailures: " ++ show numFailures)

main :: IO ()
main =
  executeAndReport (doTest <$> allTests)
