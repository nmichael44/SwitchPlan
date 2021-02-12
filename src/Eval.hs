{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}

module Eval where

import Switch
import qualified Data.Bits as Bits
import qualified Data.Map.Lazy as M
import qualified Data.Maybe as Maybe

eval :: Platform -> SwitchPlan -> Integer -> Either String Label
eval platform plan n = go plan
  where
    (Platform bytesInWord) = platform
    bitsInWord = 8 * bytesInWord
    msb = 1 `Bits.shiftL` (bitsInWord - 1)

    go :: SwitchPlan -> Either String Label
    go (Unconditionally label) = Right label

    go (IfEqual k label otherPlan)
      = if n == k then Right label else go otherPlan
    
    go (IfLT _signed k thenPlan elsePlan)
      = go $ if n < k then thenPlan else elsePlan
    
    go (IfLE _signed k thenPlan elsePlan)
      = go $ if n <= k then thenPlan else elsePlan

    go (BitTest BitTestInfo { offset, magicConstant, bitTestFailedPlan } bitTestSucceededPlan)
        = go $ if ((magicConstant `Bits.shiftL` fromIntegral (n - Maybe.fromMaybe 0 offset)) Bits..&. msb) /= 0
              then bitTestSucceededPlan
              else bitTestFailedPlan

    go (JumpTable (SwitchTargets _signed _range defLabelOpt intToLabel _ _))
      = case M.lookup n intToLabel of
          Nothing -> case defLabelOpt of { Just lab -> Right lab; Nothing -> Left ("Bad plan.  Could not find int " ++ show n ++ " in cases and there was no default label.") }
          Just lab -> Right lab
