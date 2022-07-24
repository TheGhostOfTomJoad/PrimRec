module Syntax (Ty (..), ExpN (..)) where

import Lib.Nat (Nat)

data Ty = TyNat | (:->) Ty Ty | TyList Nat Ty | TyPrec Nat

--  deriving (Show, Eq)
data ExpN
  = NatN Integer
  | LetN String ExpN ExpN
  | LamN String Ty ExpN
  | VarN String
  | AppN ExpN ExpN
  | NilN (Maybe Ty)
  | ConsN ExpN ExpN
  | ConstZeroN Int
  | SuccN
  | ProjN Int Int
  | PRecN ExpN ExpN
  | CompN ExpN ExpN
  | RunPrekN ExpN
