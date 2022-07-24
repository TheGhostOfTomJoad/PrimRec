{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module ScopeCheck (scopeCheckClosed, ExpSC (..), scopeCheck, CheckM) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Kind (Type)
import Lib.Fin
import Lib.HReader
import Lib.Nat
import qualified Lib.Nat as Nat
import Lib.SNat
import qualified Lib.SNat as SNat
import Lib.Vector
import Precs
import Prettyprinter
import Syntax
import Types

data ExpSC :: Nat -> Type where
  NatSC :: Integer -> ExpSC n
  LetSC :: ExpSC n -> ExpSC (S n) -> ExpSC n
  LamSC :: STy a -> ExpSC (S n) -> ExpSC n
  VarSC :: Fin n -> ExpSC n
  AppSC :: ExpSC n -> ExpSC n -> ExpSC n
  NilSC :: Maybe (STy a) -> ExpSC n -- empty list must be annotated
  ConsSC :: ExpSC n -> ExpSC n -> ExpSC n
  BasePRecSC :: SNat m -> PR m -> ExpSC n
  PRecSC :: ExpSC n -> ExpSC n -> ExpSC n
  CompSC :: ExpSC n -> ExpSC n -> ExpSC n
  RunPrekSC :: ExpSC n -> ExpSC n

type CheckM n e ann a = ReaderT e (Except (Doc ann)) a

type ScopeCheckM n ann a = CheckM n (Vec n String) ann a

bindSC :: String -> ScopeCheckM (S n) ann a -> ScopeCheckM n ann a
bindSC bound_var = hlocal (bound_var :>)

sCHelper :: ExpN -> ScopeCheckM n ann (ExpSC n)
sCHelper (LetN s t1 t2) = do
  t1' <- sCHelper t1
  t2' <- bindSC s $ sCHelper t2
  return $ LetSC t1' t2'
sCHelper (NatN n) = return $ NatSC n
sCHelper (LamN s ty t) = do
  ATy sTy <- return $ tyToSTy ty
  tSC <- bindSC s $ sCHelper t
  return $ LamSC sTy tSC
sCHelper (LamN s ty t) = do
  tSC <- bindSC s $ sCHelper t
  tyToStyCPS ty (\sTy -> return $ LamSC sTy tSC)
sCHelper (VarN s) =
  do
    varNames <- ask
    case index s varNames of
      Nothing -> throwError $ "unbound variable" <+> pretty s
      Just fin -> return $ VarSC fin
sCHelper (AppN t1 t2) =
  AppSC <$> sCHelper t1 <*> sCHelper t2
sCHelper (NilN maybeTy) = case tyToSTy <$> maybeTy of
  Nothing -> return $ NilSC Nothing
  Just (ATy ty) -> return $ NilSC $ return ty
sCHelper (NilN maybeTy) = case maybeTy of
  Nothing -> return $ NilSC Nothing
  Just ty -> tyToStyCPS ty (return . NilSC . Just)
sCHelper (ConsN x xs) = do
  x' <- sCHelper x
  xs' <- sCHelper xs
  return $ ConsSC x' xs'
sCHelper (ConstZeroN n) = SNat.fromNatCPS (Nat.fromInt n) (\sn -> return $ BasePRecSC sn ConstZero)
sCHelper (ConstZeroN n) = case toEnum n of
  ASNat na -> return $ BasePRecSC na ConstZero
sCHelper (ConstZeroN n) =
  SNat.fromIntCPS
    n
    ( \sn ->
        return $ BasePRecSC sn ConstZero
    )
sCHelper SuccN = return $ BasePRecSC (Sy SZ) Succ
sCHelper (ProjN arity pIndex) = do
  (AFinSNat arity' pIndex') <- intToASNatFin arity pIndex
  return $ BasePRecSC arity' (Proj pIndex')
sCHelper (ProjN arity pIndex) =
  intToASNatFinCPS arity pIndex (\(sn, f) -> return $ BasePRecSC sn (Proj f))
sCHelper (ProjN arity pIndex) =
  intToASNatFinCPS' arity pIndex (\sn f -> return $ BasePRecSC sn (Proj f))
sCHelper (PRecN g f) =
  PRecSC <$> sCHelper g <*> sCHelper f
sCHelper (CompN g gs) = do
  g' <- sCHelper g
  gs' <- sCHelper gs
  return $ CompSC g' gs'
sCHelper (RunPrekN pr) = RunPrekSC <$> sCHelper pr

scopeCheck :: Vec n String -> ExpN -> Either (Doc ann) (ExpSC n)
scopeCheck context exp = runExcept $ runReaderT (sCHelper exp) context

scopeCheckClosed :: ExpN -> Either (Doc ann) (ExpSC Z)
scopeCheckClosed = scopeCheck VNil
