{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Interpreter (evalSafeClosed, evalSafe, prek) where

import GHC.Natural
import Lib.HList
import Lib.Types
import TypeChecker

evalSafe :: ValContext e n -> ExpTC e a -> Eval a
evalSafe e (LetTC t1 t2) = evalSafe (ID (evalSafe e t1) `HCons` e) t2
evalSafe e (VarTC n) = unID $ lkup n e
evalSafe e (AppTC f x) = evalSafe e f (evalSafe e x)
evalSafe e (LamTC b) = \x -> evalSafe (ID x `HCons` e) b
evalSafe _ SuccTC = (+ 1)
evalSafe _ (NatTC n) = n
evalSafe e (PRecTC f) = prek' (evalSafe e f)

evalSafeClosed :: ExpTC '[] a -> Eval a
evalSafeClosed = evalSafe HNil

prek :: (t -> Natural -> t) -> (t -> Natural -> t)
prek h acc y
  | y == 0 = acc
  | otherwise = h (prek h acc (y - 1)) (y - 1)

for ::
  t ->
  Natural ->
  Natural ->
  (t -> Natural -> t) ->
  t
for !acc i n h
  | i == n = acc
  | otherwise = for (h acc i) (i + 1) n h

prek' :: (t -> Natural -> t) -> t -> Natural -> t
prek' h acc counter = for acc 0 counter h
