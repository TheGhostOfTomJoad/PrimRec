module Syntax where

import Lib.Nat

data Ty = TyNat | (:->) Ty Ty | TyList Nat Ty | TyPrec Nat
  deriving (Show, Eq)

class ExpN repr where
  natN :: Integer -> repr
  letN :: String -> repr -> repr -> repr
  lamN :: String -> Ty -> repr -> repr
  varN :: String -> repr
  appN :: repr -> repr -> repr
  nilN :: Maybe Ty -> repr
  consN :: repr -> repr -> repr
  singN :: Maybe Ty -> repr -> repr
  constZeroN :: Int -> repr
  succN :: repr
  projN :: Int -> Int -> repr
  pRecN :: repr -> repr -> repr
  compN :: repr -> repr -> repr
  runPrekN :: repr -> repr
