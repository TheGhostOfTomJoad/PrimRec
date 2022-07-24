{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Precs (PR (..), evalSafePr, compArity) where

import Control.Lens ((??))
import Data.Kind (Type)
import GHC.Natural
import Lib.Fin
import Lib.Nat
import Lib.SNat
import Lib.Vector
import Test.QuickCheck

data PR :: Nat -> Type where
  Succ :: PR (S Z)
  ConstZero :: SNat n -> PR n
  Proj :: SNat n -> Fin n -> PR n
  Comp :: PR (S m) -> Vec (S m) (PR n) -> PR n
  PRec :: PR n -> PR (S (S n)) -> PR (S n)

deriving instance Show (PR n)

compArity :: PR n -> SNat n
compArity Succ = Sy SZ
compArity (ConstZero sn) = sn
compArity (Proj sn _) = sn
compArity (Comp _ (x :> _)) = compArity x
compArity (PRec g _) = Sy $ compArity g

evalSafePr :: PR n -> Vec n Natural -> Natural
evalSafePr (ConstZero _) = const 0
evalSafePr Succ = (+ 1) . safeHead
evalSafePr (Proj _ f) = (!!! f)
evalSafePr (Comp h gList) =
  evalSafePr h . (??) (fmap evalSafePr gList)
evalSafePr (PRec g h) =
  -- Order of Arguments like in the English Wikipedia
  paraNat (evalSafePr g) (evalSafePr h)

instance (Arbitrary (SNat (S (S n))), Arbitrary (Fin (S n)), Arbitrary (PR ('S n))) => Arbitrary (PR (S (S n))) where
  arbitrary =
    oneof
      [ ConstZero <$> arbitrary,
        Proj <$> arbitrary <*> arbitrary,
        PRec <$> arbitrary <*> arbitrary
      ]

instance Arbitrary (PR Z) where
  arbitrary =
    oneof
      [ return $ ConstZero SZ
      ]

instance Arbitrary (PR (S Z)) where
  arbitrary =
    oneof
      [ return $ ConstZero (Sy SZ),
        return Succ,
        return (Proj (Sy SZ) FZero),
        PRec <$> arbitrary <*> arbitrary
      ]
