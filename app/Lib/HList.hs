{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lib.HList where

import Data.Kind
import Lib.Fin
import Lib.Vector
import Syntax
import Types (Eval, STy (STyNat))

-- similiar to this
-- https://hengchu.github.io/posts/2018-05-09-type-lists-and-type-classes.lhs.html
data HList :: forall n. (k -> Type) -> Vec n k -> Type where
  HNil :: HList f VNil
  HCons :: f x -> HList f xs -> HList f (x :> xs)

data Index :: forall n. Vec n k -> k -> Type where
  ZeroI :: Index (a :> b) a
  SuccI :: Index e a -> Index (b :> e) a

lkup :: Index v k -> HList f v -> f k
lkup ZeroI (HCons x _) = x
lkup (SuccI n) (HCons _ xs) = lkup n xs

finToIndexCPS ::
  forall n b (env :: Vec n Ty).
  Fin n ->
  HList STy env ->
  (forall a. Index env a -> STy a -> b) ->
  b
finToIndexCPS FZero (HCons sTy _) g = g ZeroI sTy
finToIndexCPS (FSuc n) (HCons _ env) g = finToIndexCPS n env (g . SuccI)

type STyContext e = HList STy e

xs :: STyContext (TyNat :> VNil)
xs = HCons STyNat HNil

newtype ID a = ID {unID :: Eval a}

type ValContext e = HList ID e

zs :: ValContext (TyNat :> VNil)
zs = HCons (ID 5) HNil

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
