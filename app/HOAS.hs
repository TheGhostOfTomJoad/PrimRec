{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module HOAS where

import Data.Kind
import Interpreter (prek)
import Lib.HList
import Lib.Nat
import qualified Lib.Vector
import Syntax
import TypeChecker
import Types

data ExpTCH :: Ty -> Type where
  -- NatTCH :: Natural -> ExpTCH TyNat
  LetTCH :: ExpTCH a -> (ExpTCH a -> ExpTCH b) -> ExpTCH b
  LamTCH :: (ExpTCH a -> ExpTCH b) -> ExpTCH (a :-> b)
  AppTCH :: ExpTCH (a :-> b) -> ExpTCH a -> ExpTCH b
  SuccTCH :: ExpTCH (TyNat :-> TyNat)
  PRecTCH :: ExpTCH (a :-> (TyNat :-> a)) -> ExpTCH (a :-> (TyNat :-> a))
  Lift :: Eval a -> ExpTCH a

eval :: ExpTCH a -> Eval a
eval (Lift n) = n
eval (LamTCH f) = eval . f . Lift
eval (LetTCH x f) = eval (f x)
eval (AppTCH f x) = eval f $ eval x
eval SuccTCH = (+ 1)
eval (PRecTCH f) = prek $ eval f

dBToHoas ::
  forall (n :: Nat) (env :: Ctx n) (ty :: Ty).
  HList ExpTCH env ->
  ExpTC env ty ->
  ExpTCH ty
dBToHoas _ (NatTC n) = Lift n
dBToHoas env (LetTC t1 t2) =
  let t1' = dBToHoas env t1
      t2' = dBToHoas (HCons t1' env) t2
   in t2'
dBToHoas env (LetTC t1 t2) =
  let t1' = dBToHoas env t1
      f t = dBToHoas (HCons t env) t2
   in LetTCH t1' f
dBToHoas env (LamTC exp) =
  let f t = dBToHoas (HCons t env) exp
   in LamTCH f
dBToHoas env (VarTC index) = lkup index env
dBToHoas env (AppTC f x) = AppTCH (dBToHoas env f) (dBToHoas env x)
dBToHoas _ SuccTC = SuccTCH
dBToHoas env (PRecTC f) = PRecTCH $ dBToHoas env f

type HoasContext xs = HList ExpTCH xs

eval' :: ExpTC 'Lib.Vector.VNil ty -> ExpTCH ty
eval' = dBToHoas HNil
