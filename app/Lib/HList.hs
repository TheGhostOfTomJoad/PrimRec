{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lib.HList (HList (..), lkup, finToIndexCPS, Index (..)) where

import Data.Kind
import Lib.Fin
import Lib.Nat
import Prettyprinter

-- https://hengchu.github.io/posts/2018-05-09-type-lists-and-type-classes.lhs.html
data HList :: (k -> Type) -> [k] -> Nat -> Type where
  HNil :: HList f '[] Z
  HCons :: f x -> HList f xs n -> HList f (x : xs) (S n)

data Index :: [k] -> k -> Type where
  ZeroI :: Index (a : b) a
  SuccI :: Index e a -> Index (b : e) a

instance (Show (Index env a)) where
  show = show . indexToInt

instance Pretty (Index env a) where
  pretty = pretty . indexToInt

indexToInt :: forall k (a :: [k]) (b :: k). Index a b -> Int
indexToInt ZeroI = 0
indexToInt (SuccI n) = (+ 1) $ indexToInt n

lkup :: Index v k -> HList f v n -> f k
lkup ZeroI (HCons x _) = x
lkup (SuccI n) (HCons _ xs) = lkup n xs

finToIndexCPS ::
  forall n b a f (env :: [a]).
  Fin n ->
  HList f env n ->
  (forall a. Index env a -> f a -> b) ->
  b
finToIndexCPS FZero (HCons sTy _) g = g ZeroI sTy
finToIndexCPS (FSuc n) (HCons _ env) g = finToIndexCPS n env (g . SuccI)

-- zs :: ValContext (TyNat :> VNil)
-- zs = HCons (ID 5) HNil

-- type ValContextV e = HList Val e

-- ys :: HList Val (TyNat :> VNil)
-- ys = HCons (NatV 5) HNil

-- newtype ID' a = ID' {unID' :: a}

-- xs' :: HList ID' (Int ':> 'VNil)
-- xs' = HCons (ID' 5) HNil

-- data HList :: forall n. (Ty -> Type) -> Vec n Ty -> Type where
--   HNil  :: HList f VNil
--   HCons :: f x -> HList f  xs -> HList f (x :> xs)

-- data Index :: forall n. Vec n Ty -> Ty -> Type where
--   ZeroI :: Index (a :> b) a
--   SuccI :: Index e a -> Index (b :> e) a

-- lkup :: Index v k -> HList f v -> f k
-- lkup ZeroI (HCons x _) = x
-- lkup  (SuccI n) (HCons _ xs) = lkup n xs

-- data ID :: Ty -> Type where
--   ID :: Eval a -> ID a
