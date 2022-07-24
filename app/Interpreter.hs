{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Interpreter (evalSafeClosed, evalSafe) where

import Lib.Vector
import Precs
import TypeChecker
import Types

evalSafe :: ValContext env -> ExpTC env ty -> Eval ty
evalSafe _ (NatTC n) = n
evalSafe env (LetTC t1 t2) = evalSafe (evalSafe env t1 `ExtendVC` env) t2
evalSafe env (LamTC b) = \x -> evalSafe (x `ExtendVC` env) b
evalSafe env (VarTC n) = lookupVar n env
evalSafe env (AppTC f x) = evalSafe env f (evalSafe env x)
evalSafe _ NilTC = VNil
evalSafe env (ConsTC x xs) = evalSafe env x :> evalSafe env xs
evalSafe _ (BasePRecTC pr) = pr
evalSafe env (CompTC f gList) = Comp (evalSafe env f) (evalSafe env gList)
evalSafe env (PRecTC g f) = PRec (evalSafe env g) (evalSafe env f)
evalSafe env (RunPrecTC pr) = evalSafePr (evalSafe env pr)
evalSafe env (LetTC t1 t2) =
  let x = evalSafe env t1 -- evalSafe (evalSafe env t1 `ExtendVC` env) t2
   in evalSafe (x `ExtendVC` env) t2

evalSafeClosed :: ExpTC VNil a -> Eval a
evalSafeClosed = evalSafe EmptyVC
