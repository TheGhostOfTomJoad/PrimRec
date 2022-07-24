{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module PrecsGen where

import Control.Lens ((??))
import Data.Kind

data Nat = Z | S Nat
  deriving (Show, Eq)

data Fin :: Nat -> Type where
  FZero :: Fin (S n)
  FSuc :: Fin n -> Fin (S n)

data Vec :: Nat -> Type -> Type where
  VNil :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a

(!) :: Vec n a -> Fin n -> a
(x :> _) ! FZero = x
(_ :> xs) ! FSuc n = xs ! n

class PRSem a where
  zero :: a
  isZero :: a -> Bool
  succ' :: ArgsOfSuc a -> a -> a
  type ArgsOfSuc a :: Type
  pred' :: a -> a

data PR :: Nat -> Type -> Type where
  Succ :: ArgsOfSuc a -> PR (S Z) a
  ConstZero :: PR n a
  Proj :: Fin n -> PR n a
  Comp :: PR m a -> Vec m (PR n a) -> PR n a
  PRec :: PR n a -> PR (S (S n)) a -> PR (S n) a

deriving instance Functor (Vec n)

safeHead :: Vec (S n) a -> a
safeHead (x :> _) = x

evalSafePr :: PRSem a => PR n a -> ArithFun n a
evalSafePr ConstZero = const zero
evalSafePr (Succ argsOfSuc) = succ' argsOfSuc . safeHead
evalSafePr (Proj n) = (! n)
evalSafePr (Comp h gList) =
  evalSafePr h . (??) (fmap evalSafePr gList)
evalSafePr (PRec g h) =
  -- Order of Arguments like in the English Wikipedia
  para (evalSafePr g) (evalSafePr h)

type ArithFun n a = Vec n a -> a

para ::
  PRSem a =>
  ArithFun n a ->
  ArithFun (S (S n)) a ->
  ArithFun (S n) a
para g h (x :> xs) =
  if isZero x
    then g xs
    else let smaller = (pred' x :> xs) in h $ para g h smaller :> smaller

prec :: (PRSem a) => (a -> t -> t) -> a -> t -> t
prec f x acc = if isZero x then acc else prec f (pred' x) (f x acc)

plus :: PR ('S ('S n)) Integer
plus = PRec (Proj FZero) (Comp (Succ ()) ((:>) (Proj FZero) VNil))

plusS :: PR ('S ('S n)) String
plusS = PRec (Proj FZero) (Comp (Succ 'a') ((:>) (Proj FZero) VNil))

plusOne :: PR (S Z) Integer
plusOne = Succ ()

prepA :: PR (S Z) String
prepA = Succ 'a'

instance PRSem [a] where
  zero = []
  isZero [] = True
  isZero _ = False
  type ArgsOfSuc [a] = a
  succ' x xs = x : xs
  pred' (x : xs) = xs
  pred' [] = []

instance PRSem Integer where
  zero = 0
  isZero 0 = True
  isZero _ = False
  type ArgsOfSuc Integer = ()
  succ' () x = x + 1
  pred' x = x -1

instance PRSem String where
  zero = ""
  isZero "" = True
  isZero _ = False
  type ArgsOfSuc String = Char
  succ' x xs = x : xs
  pred' (x : xs) = xs
  pred' "" = []
