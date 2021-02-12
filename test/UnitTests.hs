{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE NamedFieldPuns #-}

module UnitTests where

import qualified Data.Map.Lazy as M
import qualified Data.Set as S
import qualified Data.Maybe as Maybe
import qualified Switch as SW
import qualified Eval as EV
import qualified Utils as U

import Debug.Trace ( trace )

type Label = SW.Label 

data PieceOfCase
  = C Integer Label  -- usual case i.e. n -> L1
  | D Label       -- the default case

newtype DataTypeRange = DTR (Integer, Integer)
newtype TestingRange = TR (Integer, Integer)

data TestInputs = TI [PieceOfCase] DataTypeRange TestingRange SW.Platform
data TestCase = TC DataTypeRange TestingRange SW.SwitchTargets SW.Platform

mkTestCase :: TestInputs -> TestCase
mkTestCase (TI cases dtr@(DTR (lb, ub)) tr@(TR (testLb, testUb)) platform)
  = let
      fullSet = S.fromAscList [lb..ub]
      intToLabel =
        case U.buildMap (cases >>=  (\case { (C i l) -> [(i, l)]; (D _) -> [] })) of
          Left err -> error err
          Right m -> m
      numCases = M.size intToLabel

      defaults = concatMap (\case { (C _ _) -> []; (D l)-> [l] }) cases
      numDefaults = length defaults
    in
      if | lb > ub -> error "Bad data type range."
         | testLb > testUb -> error "Bad test range."
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
             TC dtr tr st platform

doTest :: TestCase -> IO ()
doTest (TC (DTR (lb, ub)) (TR (testLb, testUb)) st platform)
  = print plan
  where
    plan = SW.createPlan st platform

lab0 :: SW.Label
lab0 = SW.L 0
lab1 :: SW.Label
lab1 = SW.L 1

sPlatform :: SW.Platform
sPlatform = SW.Platform SW.bytesInWordForPlatform


test0_size_1 :: TestCase
test0_size_1 = mkTestCase (TI [C 0 lab0, D lab1] (DTR (0, 0)) (TR (-2, 2)) sPlatform)
test1_size_1 :: TestCase
test1_size_1 = mkTestCase (TI [C 1 lab0, D lab1] (DTR (0, 1)) (TR (-2, 2)) sPlatform)
test2_size_1 :: TestCase
test2_size_1 = mkTestCase (TI [C 1 lab0, D lab1] (DTR (0, 5)) (TR (-2, 7)) sPlatform)

