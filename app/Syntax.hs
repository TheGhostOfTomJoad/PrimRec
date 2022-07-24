module Syntax (Ty (..), ExpN (..)) where

import GHC.Natural (Natural)

data Ty = TyNat | (:->) Ty Ty
  deriving (Show, Eq)

data ExpN
  = SuccN
  | LetN String ExpN ExpN
  | VarN String
  | AppN ExpN ExpN
  | LamN String Ty ExpN
  | NatN Natural
  | PRecN ExpN
  deriving (Show, Eq)
