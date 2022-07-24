{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Lib.Vector (Vec (..), paraNat, (!!!), len, index, uncurry', Curry, ArithFun, safeHead) where

-- Contains code for Lists
-- that know their lenght

import Data.Kind (Type)
import Lib.Fin
import Lib.Nat
import Lib.SNat
import Test.QuickCheck

--- source: https://softwareengineering.stackexchange.com/questions/276867/is-it-possible-to-bake-dimension-into-a-type-in-haskell

data Vec :: Nat -> Type -> Type where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a

infixr 5 :>

deriving instance (Show a) => Show (Vec n a)

deriving instance (Functor (Vec n))

deriving instance (Foldable (Vec n))

instance Arbitrary (Vec Z Integer) where
  arbitrary = return VNil

instance Arbitrary (Vec n Integer) => Arbitrary (Vec (S n) Integer) where
  arbitrary = do
    Positive x <- arbitrary
    xs <- arbitrary
    return $ x :> xs

(!!!) :: Vec n a -> Fin n -> a
(x :> _) !!! FZero = x
(_ :> xs) !!! FSuc n = xs !!! n

-- VNil !!! n = case n of

--
--
--

index :: Eq a => a -> Vec n a -> Maybe (Fin n)
index _ VNil = Nothing
index el (x :> _) | el == x = return FZero
index el (_ :> xs) = FSuc <$> index el xs

len :: Vec n a -> SNat n
len VNil = SZ
len (_ :> xs) = Sy $ len xs

type ArithFun n = (Vec n Integer -> Integer)

paraNat ::
  ArithFun n ->
  ArithFun (S (S n)) ->
  ArithFun (S n)
paraNat g h (x :> xs) = case x of
  0 -> g xs
  _ -> let smaller = ((x - 1) :> xs) in h $ paraNat g h smaller :> smaller

--paraNat = paraNat''' --paraTailRec

--
--
--

for ::
  Integer ->
  Integer ->
  Integer ->
  ArithFun (S (S n)) ->
  ArithFun n
for !acc i n h vs
  | i == n = acc
  | otherwise = for (h $ acc :> (i :> vs)) (i + 1) n h vs

paraTailRec ::
  ArithFun n ->
  ArithFun (S (S n)) ->
  ArithFun (S n)
paraTailRec g h (v :> vs) = for (g vs) 0 v h vs

--
--
--
--

type Curry :: Nat -> a
type family Curry n where
  Curry Z = Integer
  Curry (S n) = Integer -> Curry n

uncurry' :: Curry n -> ArithFun n
uncurry' f VNil = f
uncurry' f (x :> xs) = uncurry' (f x) xs

curry' :: SNat n -> ArithFun n -> Curry n
curry' SZ f = f VNil
curry' (Sy n) f = \m -> curry' n (\v -> f (m :> v))

--- source: https://softwareengineering.stackexchange.com/questions/276867/is-it-possible-to-bake-dimension-into-a-type-in-haskell

arb :: SNat n -> Gen (Vec n Integer)
arb SZ = return VNil
arb (Sy n) = do
  Positive x <- arbitrary
  xs <- arb n
  return $ x :> xs

paraNat' :: (a -> b) -> (b -> Integer -> a -> b) -> Integer -> a -> b
paraNat' g _ 0 xs = g xs
paraNat' g h x xs =
  h (paraNat' g h (x - 1) xs) (x - 1) xs

paraNat'' :: (a -> Integer -> a) -> Integer -> a -> a
paraNat'' _ 0 acc = acc
paraNat'' h x acc =
  h (paraNat'' h (x - 1) acc) (x - 1)

safeHead :: Vec (S n) a -> a
safeHead (x :> _) = x

paraNat''' ::
  ArithFun n ->
  ArithFun (S (S n)) ->
  ArithFun (S n)
paraNat''' g h (x :> xs) =
  paraNat'' (\acc counter -> h (acc :> (counter :> xs))) x (g xs)