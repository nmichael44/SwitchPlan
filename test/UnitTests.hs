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
       when (numDefaults == 0) (when (testLb < lb || testUb > ub) (Left "When default label is missing, you cannot test outside the datatype range."))
       when (numCases == 0) $ Left "No cases specified."
       when (numDefaults > 1) $ Left "Too many defaults."
       when (numCases == 1 && numDefaults == 0) $ Left "Missing default case."
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
      when sShowPlans (putStrLn $ "Plan: " ++ show plan)
      let res = Maybe.catMaybes $ processRes <$> diffs
      if null res then do { putStrLn "Ok!\n"; return True } else do { putStrLn ""; mapM_ putStrLn res; return False }
  where
    plan = SW.createPlan st platform
    eval = EV.eval platform plan
    diffs = [(n, expected, res) | n <- [testLb..testUb], let expected = lookup n intToLabel defLabelOpt, let res = eval n]

    processRes :: (Integer, Label, Either String Label) -> Maybe String
    processRes (n, expectedLabel, Left errStr) = Just $ "For n: " ++ show n ++ " expected: " ++ show expectedLabel ++ " but instead got an error: \"" ++ errStr ++ "\""
    processRes (n, expectedLabel, Right resultLabel) = if expectedLabel /= resultLabel then Just $ "For n: " ++ show n ++ " expected: " ++ show expectedLabel ++ " but instead got:"  ++ show resultLabel else Nothing

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
sPlatform = SW.Platform SW.bytesInWordForPlatform

type STC = (Int, Either String TestCase) -- Switch Test Case

test0_size_1 :: STC
test0_size_1 = mkTestCase 0 (TI [C 0 lab0, D lab1] (DTR (0, 1)) (TR (-2, 2)) sPlatform)
test1_size_1 :: STC
test1_size_1 = mkTestCase 1 (TI [C 1 lab0, D lab1] (DTR (0, 1)) (TR (-2, 2)) sPlatform)
test2_size_1 :: STC
test2_size_1 = mkTestCase 2 (TI [C 1 lab0, D lab1] (DTR (0, 5)) (TR (-2, 7)) sPlatform)

test3_size_2 :: STC
test3_size_2 = mkTestCase 3 (TI [C 0 lab0, C 1 lab1] (DTR (0, 1)) (TR (0, 1)) sPlatform)
test4_size_2 :: STC
test4_size_2 = mkTestCase 4 (TI [C 0 lab0, C 1 lab0] (DTR (0, 1)) (TR (0, 1)) sPlatform)

allTests :: [STC]
allTests = [test0_size_1, test1_size_1, test2_size_1
            , test3_size_2, test4_size_2]

executeAndReport :: [IO Bool] -> IO ()
executeAndReport actions
  = do
      results <- sequence actions
      let (numSuccesses, numFailures) = L.foldl' (\(s, f) e -> if e then (s + 1, f) else (s, f + 1)) (0, 0) results
      putStrLn ("\nResults:\nSuccesses: " ++ show numSuccesses ++ "\nFailures: " ++ show numFailures)

main :: IO ()
main =
  executeAndReport (doTest <$> allTests)
