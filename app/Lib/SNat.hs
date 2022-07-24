{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Lib.SNat (SNat (..), ASNat (ASNat), fromNat, ToInt (toInt), fromNatCPS, fromIntCPS) where

import Data.Type.Equality
import Lib.Nat (Nat (..))
import Prettyprinter

data SNat (n :: Nat) where
  SZ :: SNat Z
  Sy :: SNat n -> SNat (S n)

deriving instance Show (SNat n)

data ASNat where
  ASNat :: SNat n -> ASNat

-- data ASNat = forall n . ASNat  (SNat n)

fromNat :: Nat -> ASNat
fromNat Z = ASNat SZ
fromNat (S n) = case fromNat n of ASNat na -> ASNat $ Sy na

fromNatCPS :: Nat -> (forall n. SNat n -> t) -> t
fromNatCPS Z g = g SZ
fromNatCPS (S n) g = fromNatCPS n (g . Sy)

instance Pretty (SNat n) where
  pretty = pretty . toInt

instance TestEquality SNat where
  testEquality SZ SZ = Just Refl
  testEquality (Sy n) (Sy m) = do
    Refl <- testEquality n m
    return Refl
  testEquality _ _ = Nothing

fromInt :: Int -> ASNat
fromInt 0 = ASNat SZ
fromInt n | n < 0 = error "Only positve Integers are allowed"
fromInt n = case fromInt $ n - 1 of
  ASNat na -> ASNat (Sy na)

fromIntCPS :: Int -> (forall n. SNat n -> a) -> a
fromIntCPS 0 g = g SZ
fromIntCPS n _ | n < 0 = error "Only positve Integers are allowed"
fromIntCPS n g = fromIntCPS (n - 1) (g . Sy)

class ToInt a where
  toInt :: a -> Int

instance ToInt (SNat n) where
  toInt SZ = 0
  toInt (Sy n) = 1 + toInt n

instance Enum ASNat where
  toEnum = fromInt
  fromEnum (ASNat sn) = toInt sn
