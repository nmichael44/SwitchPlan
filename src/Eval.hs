{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}

module Eval where

import Switch
import Data.Bits
import qualified Data.Map.Lazy as M
import Data.Maybe(fromMaybe)

eval :: Platform -> SwitchPlan -> Integer -> Label
eval platform plan n = go plan
  where
    (Platform bytesInWord) = platform
    msb = 1 `shiftL` (8 * bytesInWord - 1)

    go :: SwitchPlan -> Label
    go (Unconditionally label) = label

    go (IfEqual k label otherPlan)
      = if n == k then label else go otherPlan
    
    go (IfLT _signed k thenPlan elsePlan)
      = go $ if n < k then thenPlan else elsePlan
    
    go (IfLE _signed k thenPlan elsePlan)
      = go $ if n <= k then thenPlan else elsePlan

    go (BitTest
         BTOI {
           bitTestInfo = BitTestInfo { offset, magicConstant, bitTestFailedPlan }
           , bitTestSucceededPlan })
      = go $ if ((magicConstant `shiftL` fromIntegral (n - fromMaybe 0 offset)) .&. msb) /= 0
             then bitTestSucceededPlan
             else bitTestFailedPlan

    go (JumpTable (SwitchTargets signed (lb, ub) defLabelOpt intToLabel _ _))
      = case M.lookup n intToLabel of
          Nothing -> case defLabelOpt of { Just lab -> lab; Nothing -> error "Bad plan" }
          Just lab -> lab
