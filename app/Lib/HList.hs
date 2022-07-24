{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lib.HList where

import Data.Kind
import Lib.Vector
import Types

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

type STyContext e = HList STy e

newtype ID' a = ID' {unID' :: a}

xs' :: HList ID' (Int ':> 'VNil)
xs' = HCons (ID' 5) HNil
