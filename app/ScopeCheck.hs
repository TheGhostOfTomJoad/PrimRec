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
import GHC.Natural (Natural)
import Lib.Fin
import Lib.HReader
import Lib.Nat
import Lib.Vector
import Prettyprinter
import Syntax
import Types

data ExpSC :: Nat -> Type where
  SuccSC :: ExpSC n
  LetSC :: ExpSC n -> ExpSC (S n) -> ExpSC n
  VarSC :: Fin n -> ExpSC n
  AppSC :: ExpSC n -> ExpSC n -> ExpSC n
  LamSC :: STy a -> ExpSC (S n) -> ExpSC n
  NatSC :: Natural -> ExpSC n
  PRecSC :: ExpSC n -> ExpSC n

type CheckM n e ann a = ReaderT e (Except (Doc ann)) a

type ScopeCheckM n ann a = CheckM n (Vec n String) ann a

bindSC :: String -> ScopeCheckM (S n) ann a -> ScopeCheckM n ann a
bindSC bound_var = hlocal (bound_var :>)

sCHelper :: ExpN -> ScopeCheckM n ann (ExpSC n)
sCHelper SuccN = return SuccSC
sCHelper (LetN s t1 t2) = do
  t1' <- sCHelper t1
  t2' <- bindSC s $ sCHelper t2
  return $ LetSC t1' t2'
sCHelper (VarN n) =
  do
    varNames <- ask
    case index n varNames of
      Nothing -> throwError $ "unbound variable" <+> pretty n
      Just fin -> return $ VarSC fin
sCHelper (AppN t1 t2) =
  AppSC <$> sCHelper t1 <*> sCHelper t2
sCHelper (LamN s ty t) = do
  ATy ty' <- return $ tyToSTy ty
  t' <- bindSC s $ sCHelper t
  return $ LamSC ty' t'
sCHelper (NatN n) = return $ NatSC n
sCHelper (PRecN f) =
  PRecSC <$> sCHelper f

scopeCheck :: Vec n String -> ExpN -> Either (Doc ann) (ExpSC n)
scopeCheck context exp = runExcept $ runReaderT (sCHelper exp) context

scopeCheckClosed :: ExpN -> Either (Doc ann) (ExpSC Z)
scopeCheckClosed = scopeCheck VNil
