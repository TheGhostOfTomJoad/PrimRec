{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module Lib.Nat (Nat (..), fromInt) where

data Nat = Z | S Nat
  deriving (Show, Eq)

fromInt :: (Num t, Ord t) => t -> Nat
fromInt 0 = Z
fromInt n | n > 0 = S $ fromInt (n - 1)
fromInt _ = error "Only positve Integers are allowed"
