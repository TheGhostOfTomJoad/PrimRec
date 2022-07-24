{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Lib.Vector (Vec (..), paraNat, (!!!), len, index, uncurry', Curry, ArithFun, curry', safeHead) where

-- import           Control.Monad.Except
-- import           Data.Foldable

import Data.Kind (Type)
import qualified Debug.Trace as Debug
import GHC.Natural (Natural)
import Lib.Fin
import Lib.Nat
import Lib.SNat
import Test.QuickCheck
import Test.QuickCheck.Instances.Natural ()

--- source: https://softwareengineering.stackexchange.com/questions/276867/is-it-possible-to-bake-dimension-into-a-type-in-haskell

data Vec :: Nat -> Type -> Type where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a

infixr 5 :>

deriving instance (Show a) => Show (Vec n a)

deriving instance (Functor (Vec n))

deriving instance (Foldable (Vec n))

instance Arbitrary (Vec Z Natural) where
  arbitrary = return VNil

-- instance Arbitrary Natural where
--   arbitrary = do Positive x <- arbitrary
--                  return $ fromInteger   x
-- deriving instance CoArbitrary    (Natural)

instance Arbitrary (Vec n Natural) => Arbitrary (Vec (S n) Natural) where
  arbitrary = do
    Positive x <- arbitrary
    xs <- arbitrary
    return $ x :> xs

(!!!) :: Vec n a -> Fin n -> a
(x :> _) !!! FZero = x
(_ :> xs) !!! FSuc n = xs !!! n

-- VNil !!! n = case n of

mapV :: (a -> b) -> Vec n a -> Vec n b
mapV _ VNil = VNil
mapV f (x :> xs) = f x :> mapV f xs

index :: Eq a => a -> Vec n a -> Maybe (Fin n)
index _ VNil = Nothing
index el (x :> _) | el == x = return FZero
index el (_ :> xs) = FSuc <$> index el xs

len :: Vec n a -> SNat n
len VNil = SZ
len (_ :> xs) = Sy $ len xs

type ArithFun n = (Vec n Natural -> Natural)

paraNat ::
  ArithFun n ->
  ArithFun (S (S n)) ->
  ArithFun (S n)
--paraNat g h (x :> xs) = paraNat'' (\acc counter -> h (acc :> (counter :> xs))) x (g xs)

paraNat g h (x :> xs) = case x of
  0 -> g xs
  _ -> let smaller = ((x - 1) :> xs) in h $ paraNat g h smaller :> smaller

paraNat''''' ::
  ArithFun n ->
  ArithFun (S (S n)) ->
  ArithFun (S n)
paraNat''''' g h (x :> xs) = paraNat'' (\counter acc -> h (counter :> (acc :> xs))) x (g xs)

foldrV :: (a -> b -> b) -> b -> Vec n a -> b
foldrV _ acc VNil = acc
foldrV f acc (x :> xs) = f x (foldrV f acc xs)

for ::
  Natural ->
  Natural ->
  Natural ->
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

type Curry :: Nat -> a
type family Curry (n :: Nat) = res | res -> n where
  Curry Z = Natural
  Curry (S n) = Natural -> Curry n

uncurry' :: Curry n -> ArithFun n
uncurry' f VNil = f
uncurry' f (x :> xs) = uncurry' (f x) xs

curry' :: SNat n -> ArithFun n -> Curry n
curry' SZ f = f VNil
curry' (Sy n) f = \m -> curry' n (\v -> f (m :> v))

--- source: https://softwareengineering.stackexchange.com/questions/276867/is-it-possible-to-bake-dimension-into-a-type-in-haskell

arb :: SNat n -> Gen (Vec n Natural)
arb SZ = return VNil
arb (Sy n) = do
  Positive x <- arbitrary
  xs <- arb n
  return $ x :> xs

paraNat' :: (a -> b) -> (b -> Int -> a -> b) -> Int -> a -> b
paraNat' g _ 0 xs = g xs
paraNat' g h x xs =
  h (paraNat' g h (x - 1) xs) (x - 1) xs

paraNat'' :: (a -> Natural -> a) -> Natural -> a -> a
paraNat'' _ 0 acc = acc
paraNat'' h x acc =
  h (paraNat'' h (x - 1) acc) (x - 1)

safeHead :: Vec (S n) a -> a
safeHead (x :> _) = x

prop_EqPara :: ArithFun n -> ArithFun ('S ('S n)) -> Vec ('S n) Natural -> Bool
prop_EqPara g h xs = paraNat g h (Debug.trace (show xs) xs) == paraNat''''' g h xs

prop_EqPara' :: SNat n -> ArithFun n -> ArithFun ('S ('S n)) -> Vec ('S n) Natural -> Bool
prop_EqPara' sn = prop_EqPara

testPara :: IO ()
testPara = quickCheck (prop_EqPara' (Sy $ Sy $ Sy $ Sy SZ))

testPara' :: Arbitrary (Vec n Natural) => SNat n -> IO ()
testPara' sn = quickCheck (prop_EqPara' sn)

instance Show (a -> b) where
  show _ = "function"

instance CoArbitrary a => CoArbitrary (Vec n a) where
  coarbitrary VNil = variant 0
  coarbitrary (x :> xs) = variant 1 . coarbitrary (x, xs)

helper :: (Vec ('S ('S n)) a -> t) -> Vec n a -> a -> a -> t
helper h consts n m = h (n :> m :> consts)
