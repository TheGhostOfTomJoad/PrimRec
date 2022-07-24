{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Lib.Fin (Fin (..), liftF, AFinSNat (..), intToASNatFin, intToASNatFinCPS') where

import Control.Monad.Except
import Data.Kind (Type)
import Lib.Nat
import Lib.SNat
import Prettyprinter

data Fin :: Nat -> Type where
  FZero :: Fin (S n)
  FSuc :: Fin n -> Fin (S n)

deriving instance (Show (Fin n))

instance Pretty (Fin n) where
  pretty f = pretty (1 + toInt f)

instance ToInt (Fin n) where
  toInt FZero = 0
  toInt (FSuc f) = 1 + toInt f

liftF :: Fin n -> Fin (S n)
liftF FZero = FZero
liftF (FSuc fin) = FSuc $ liftF fin

data AFinSNat where
  AFinSNat :: SNat (S n) -> Fin (S n) -> AFinSNat

conversionHelper :: (forall n. Fin (S n) -> Fin (S (S n))) -> AFinSNat -> AFinSNat
conversionHelper f (AFinSNat na fin) = AFinSNat (Sy na) (f fin)

intToASNatFin :: (MonadError (Doc ann) f) => Int -> Int -> f AFinSNat
intToASNatFin 0 _ = throwError "artiy 0 is not not allowed for projections"
intToASNatFin _ 0 = throwError "index 0 is not not allowed for projections"
intToASNatFin 1 1 = return $ AFinSNat (Sy SZ) FZero
intToASNatFin 1 _ = throwError "the arity of an projection must be greater than or equal to the index"
intToASNatFin n 1 = conversionHelper liftF <$> intToASNatFin (n - 1) 1
intToASNatFin nna nf = conversionHelper FSuc <$> intToASNatFin (nna - 1) (nf - 1)

intToASNatFinCPS' :: (MonadError (Doc ann) f) => Int -> Int -> (forall n. SNat ('S n) -> Fin ('S n) -> f t) -> f t
intToASNatFinCPS' 0 _ _ = throwError "artiy 0 is not not allowed for projections"
intToASNatFinCPS' _ 0 _ = throwError "index 0 is not not allowed for projections"
intToASNatFinCPS' 1 1 g = g (Sy SZ) FZero
intToASNatFinCPS' 1 _ _ = throwError "the arity of an projection must be greater than or equal to the index"
intToASNatFinCPS' n 1 g = intToASNatFinCPS' (n - 1) n (\sn f -> g (Sy sn) (liftF f))
intToASNatFinCPS' nna nf g = intToASNatFinCPS' (nna - 1) (nf - 1) (\sn f -> g (Sy sn) (FSuc f))
