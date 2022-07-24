{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module TypeCheck (ExpTC (..), AExpTC (..), typeCheck, plus) where

import Data.Data
import Data.Kind
import Data.Type.Equality
import Lib.Fin
import Lib.Nat
import Lib.SNat
import Lib.Vector
import ScopeCheck
import Syntax
import Types

convertDB ::
  forall n (repr :: forall n. Ctx n -> Ty -> Type) (env :: Ctx n).
  (ExpTC repr) =>
  Fin n ->
  STyContext env ->
  AExpTC repr env
convertDB FZero (ExtendSTyC ty _) = AExpTC ty z
convertDB (FSuc n) (ExtendSTyC _ env) = case convertDB n env of
  AExpTC ty' recRes' -> AExpTC ty' $ s recRes'

type ExpTC :: (forall n. Ctx n -> Ty -> Type) -> Constraint
class ExpTC repr where
  nat :: Integer -> repr env TyNat
  let' :: repr env a -> repr (a :> env) b -> repr env b
  lam :: repr (a :> env) b -> repr env (a :-> b)
  z :: repr (a :> env) a
  s :: repr env a -> repr (b :> env) a
  app :: repr env (a :-> b) -> repr env a -> repr env b
  nil :: repr env (TyList Z a)
  cons :: repr env a -> repr env (TyList n a) -> repr env (TyList (S n) a)
  sing :: repr env a -> repr env (TyList (S Z) a)
  constZeroP :: repr env (TyPrec n)
  succP :: repr env (TyPrec (S Z))
  projP :: Fin n -> repr env (TyPrec n)
  precP ::
    repr env (TyPrec n) ->
    repr env (TyPrec (S (S n))) ->
    repr env (TyPrec (S n))
  compP ::
    repr env (TyPrec n) ->
    repr env (TyList n (TyPrec m)) ->
    repr env (TyPrec m)
  runPR :: repr env (TyPrec n) -> repr env (TyList n TyNat :-> TyNat)

data AExpTC (repr :: forall n. Ctx n -> Ty -> Type) env
  = forall a. AExpTC (STy a) (repr env a)

newtype
  ExpSC'
    ( repr ::
        forall n.
        Ctx n ->
        Ty ->
        Type
    )
    (n :: Nat) = ExpSC'
  { unExpSC' ::
      forall (env :: Ctx n).
      ExpTC repr =>
      STyContext env ->
      Maybe (AExpTC repr env)
  }

typeCheckClosed ::
  forall (repr :: forall (n :: Nat). Ctx n -> Ty -> Type).
  ExpTC repr =>
  ExpSC' repr 'Z ->
  Maybe (AExpTC repr 'VNil)
typeCheckClosed = typeCheck EmptySTyC

typeCheck ::
  forall (repr :: forall n. Ctx n -> Ty -> Type) (n :: Nat) (env :: Ctx n).
  ExpTC repr =>
  STyContext env ->
  ExpSC' repr n ->
  Maybe (AExpTC repr env)
typeCheck = flip unExpSC'

instance
  forall (repr :: forall n. Ctx n -> Ty -> Type).
  ExpSC (ExpSC' repr)
  where
  natSC n = ExpSC' $ const (return $ AExpTC STyNat (nat n))
  letSC t1 t2 = ExpSC' $ \env -> do
    (AExpTC tyF t1') <- unExpSC' t1 env
    (AExpTC tyG t2') <- unExpSC' t2 (ExtendSTyC tyF env)
    return $ AExpTC tyG (let' t1' t2')
  lamSC styA exp = ExpSC' $ \env -> do
    AExpTC sTyB expC <- unExpSC' exp (ExtendSTyC styA env)
    return $ AExpTC (styA ::-> sTyB) (lam expC)
  varSC n = ExpSC' $ \env -> return $ convertDB n env
  appSC t1 t2 = ExpSC' $ \env -> do
    AExpTC (a ::-> b) t1C <- unExpSC' t1 env
    AExpTC c t2C <- unExpSC' t2 env
    Refl <- testEquality a c
    return $ AExpTC b (app t1C t2C)
  nilSC Nothing = ExpSC' $ const Nothing
  nilSC (Just ty) = ExpSC' $ const (return $ AExpTC (STyList SZ ty) nil)
  consSC x xs = ExpSC' $ \env -> do
    AExpTC tyX xC <- unExpSC' x env
    AExpTC (STyList n tyXs) xsC <- unExpSC' xs env
    Refl <- testEquality tyX tyXs
    return $ AExpTC (STyList (Sy n) tyX) (cons xC xsC)
  singSC mTy x = ExpSC' $ \env -> do
    AExpTC tyX xC <- unExpSC' x env
    case mTy of
      Nothing -> return (AExpTC (STyList (Sy SZ) tyX) (sing xC))
      Just ty -> do
        Refl <- testEquality tyX ty
        return (AExpTC (STyList (Sy SZ) tyX) (sing xC))
  constZeroSC n = ExpSC' $ const (return $ AExpTC (STyPrec n) constZeroP)
  succSC = ExpSC' $ const (return $ AExpTC (STyPrec (Sy SZ)) succP)
  projSC fin na = ExpSC' $ const (return $ AExpTC (STyPrec na) (projP fin))
  pRecSC g gs = ExpSC' $ \env -> do
    AExpTC (STyPrec n) gC <- unExpSC' g env
    AExpTC (STyPrec (Sy (Sy m))) fC <- unExpSC' gs env
    Refl <- testEquality n m
    return $ AExpTC (STyPrec (Sy n)) (precP gC fC)
  compSC f gs = ExpSC' $ \env -> do
    AExpTC (STyPrec arityF) fC <- unExpSC' f env
    (AExpTC (STyList lenGs tyGs@(STyPrec _)) gsC) <- unExpSC' gs env
    Refl <- testEquality lenGs arityF
    return $ AExpTC tyGs (compP fC gsC)
  runPrekSC pr = ExpSC' $ \env -> do
    AExpTC (STyPrec n) prC <- unExpSC' pr env
    return $ AExpTC (STyList n STyNat ::-> STyNat) (runPR prC)

plus ::
  forall
    (repr :: forall (m :: Nat). Ctx m -> Ty -> Type)
    (env :: Ctx Z).
  ExpTC repr =>
  repr env (TyPrec (S (S Z)))
plus = precP (projP FZero) (compP succP (sing (projP FZero)))
