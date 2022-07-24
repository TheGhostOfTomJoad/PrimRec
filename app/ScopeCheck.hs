{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module ScopeCheck (scopeCheck, ExpSC (..), ExpN') where

import Control.Monad.Except
-- 

-- import Parser

import Data.Kind (Constraint, Type)
import Lib.Fin
import Lib.Nat
import Lib.SNat
import Lib.Vector
import Prettyprinter
import Syntax
import Types

type ExpSC :: ((Nat -> Type) -> Constraint)
class ExpSC repr where
  natSC :: Integer -> repr n
  letSC :: repr n -> repr (S n) -> repr n
  lamSC :: STy a -> repr (S n) -> repr n
  varSC :: Fin n -> repr n
  appSC :: repr n -> repr n -> repr n
  nilSC :: Maybe (STy a) -> repr n
  consSC :: repr n -> repr n -> repr n
  singSC :: Maybe (STy a) -> repr n -> repr n
  constZeroSC :: SNat m -> repr n
  succSC :: repr n
  projSC :: Fin m -> SNat m -> repr n
  pRecSC :: repr n -> repr n -> repr n
  compSC :: repr n -> repr n -> repr n
  runPrekSC :: repr n -> repr n

newtype ExpN' = ExpN'
  { unExpN' ::
      forall m repr n ann.
      (MonadError (Doc ann) m, ExpSC repr) =>
      Vec n String ->
      m (repr n)
  }

instance ExpN ExpN' where
  natN n = ExpN' $ const $ return $ natSC n
  letN s t1 t2 = ExpN' $ \varNames -> do
    t1' <- unExpN' t1 varNames
    t2' <- unExpN' t2 (s :> varNames)
    return $ letSC t1' t2'
  lamN s ty exp = ExpN' $ \varNames -> do
    exp' <- unExpN' exp (s :> varNames)
    case tyToSTy ty of
      ATy ty' -> return $ lamSC ty' exp'
  varN n = ExpN' $ \varNames -> do
    case index n varNames of
      Nothing -> throwError $ "unbound variable" <+> pretty n
      Just fin -> return $ varSC fin
  appN t1 t2 = ExpN' $ \varNames -> appSC <$> unExpN' t1 varNames <*> unExpN' t2 varNames
  nilN maybeTy = ExpN' $ \_ -> case tyToSTy <$> maybeTy of
    Nothing -> return $ nilSC Nothing
    Just (ATy ty) -> return $ nilSC $ return ty
  consN x xs = ExpN' $ \varNames -> do
    x' <- unExpN' x varNames
    xs' <- unExpN' xs varNames
    return $ consSC x' xs'
  singN mTy x = ExpN' $ \varNames -> do
    x' <- unExpN' x varNames
    case tyToSTy <$> mTy of
      Nothing -> return $ singSC Nothing x'
      Just (ATy sTy) -> return $ singSC (Just sTy) x'
  constZeroN n = case toEnum n of
    ASNat na -> ExpN' $ const $ return $ constZeroSC na
  succN = ExpN' $ const (return succSC)
  projN arity index =
    ExpN' $
      const
        ( do
            AFinSNat arity' index' <- intToASNatFin arity index
            return $ projSC index' arity'
        )
  pRecN f g = ExpN' $ \varNames -> pRecSC <$> unExpN' f varNames <*> unExpN' g varNames
  compN f gs = ExpN' $ \varNames -> do
    g' <- unExpN' f varNames
    gs' <- unExpN' gs varNames
    return $ compSC g' gs'
  runPrekN pr = ExpN' $ \varNames -> do
    pr' <- unExpN' pr varNames
    return $ runPrekSC pr'

scopeCheckClosed :: (MonadError (Doc ann) m, ExpSC repr) => ExpN' -> m (repr 'Z)
scopeCheckClosed = scopeCheck VNil

scopeCheck ::
  (MonadError (Doc ann) m, ExpSC repr) =>
  Vec n String ->
  ExpN' ->
  m (repr n)
scopeCheck = flip unExpN'
