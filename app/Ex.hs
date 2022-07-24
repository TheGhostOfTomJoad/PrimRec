{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Ex where -- https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Exists.hs

import Data.Kind
import Lib.Fin
import Lib.SNat
import Lib.Vector
import TypeChecker (ExpTC)
import Types (Ctx, DBIndex (..), Eval, STy, STyContext (ExtendSTyC))

data Ex :: (k -> Type) -> Type where
  Ex :: f k -> Ex f

type ASNat = Ex SNat

type ATy = Ex STy

mapEx :: (forall i. a i -> a (f i)) -> Ex a -> Ex a
mapEx f (Ex x) = Ex (f x)

inToASNat :: (Eq t, Num t) => t -> Ex SNat
inToASNat 0 = Ex SZ
inToASNat n = mapEx Sy $ inToASNat (n - 1)

data Ex2 :: (k -> Type) -> (k' -> k -> Type) -> k' -> Type where
  Ex2 :: f a -> g e a -> Ex2 f g e

data Ex2' :: (k -> Type) -> (Vec n k -> k -> Type) -> Vec n k -> Type where
  Ex2' :: f a -> g e a -> Ex2' f g e

type ADBIndex e = Ex2 STy DBIndex e

type AExpTC e = Ex2 STy ExpTC e

data Ex2'' :: (k -> Type) -> (k -> Type) -> Type where
  Ex2'' :: f a -> g a -> Ex2'' f g

newtype ID a = ID {unID :: Eval a}

type ARes = Ex2'' STy ID

convertDB :: forall n env. Fin n -> STyContext (env :: Ctx n) -> ADBIndex env
convertDB FZero (ExtendSTyC ty1 _) = Ex2 ty1 ZeroDB
convertDB (FSuc n) (ExtendSTyC _ env) = case convertDB n env of
  Ex2 sTy db -> Ex2 sTy (SuccDB db)
