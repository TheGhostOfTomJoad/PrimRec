{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Interpreter (evalSafe, ExpTC') where

import Control.Lens ((??))
import Data.Kind
import Lib.Nat
import Lib.Vector
import Syntax
import TypeCheck
import Types

type ExpTC' :: (forall n. Ctx n -> Ty -> Type)
newtype ExpTC' env a = ExpTC' {unExpTC' :: ValContext env -> Eval a}

instance ExpTC ExpTC' where
  nat x = ExpTC' $ const x
  let' t1 t2 = ExpTC' $ \e -> unExpTC' t2 (unExpTC' t1 e `ExtendVC` e)
  lam expr = ExpTC' $ \e x -> unExpTC' expr (x `ExtendVC` e)
  z = ExpTC' $ \(v `ExtendVC` _) -> v
  s n = ExpTC' $ \(_ `ExtendVC` e) -> unExpTC' n e
  app e1 e2 = ExpTC' $ \h -> unExpTC' e1 h (unExpTC' e2 h)
  nil = ExpTC' $ const VNil
  cons x xs = ExpTC' $ \e -> unExpTC' x e :> unExpTC' xs e
  sing x = ExpTC' $ \env -> unExpTC' x env :> VNil
  constZeroP = ExpTC' $ const $ PR $ const 0
  succP = ExpTC' $ const $ PR $ (+ 1) . safeHead
  projP n = ExpTC' $ const $ PR (!!! n)
  precP g h = ExpTC' $ \e -> precHelper (unExpTC' g e) (unExpTC' h e)
  compP f gs = ExpTC' $ \e -> compHelper (unExpTC' f e) (unExpTC' gs e)
  runPR pr = ExpTC' $ \env -> unPR $ unExpTC' pr env

compHelper ::
  PR n ->
  Vec n (PR m) ->
  PR m
compHelper (PR f) gs = PR $ f . (??) (fmap unPR gs)

precHelper :: PR n -> PR (S (S n)) -> PR (S n)
precHelper g h = PR $ paraNat (unPR g) (unPR h)

evalSafeClosed :: ExpTC' 'VNil a -> Eval a
evalSafeClosed = evalSafe EmptyVC

evalSafe ::
  forall (n :: Nat) (env :: Ctx n) (a :: Ty).
  ValContext env ->
  ExpTC' env a ->
  Eval a
evalSafe = flip unExpTC'

