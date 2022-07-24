{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Values where

import Control.Monad.Except
import Control.Monad.Identity
import Data.Foldable (Foldable (toList))
import Data.Kind (Type)
import Lib.Nat
import Lib.Vector
import Precs
import Pretty (prettyPR)
import Prettyprinter
import Syntax (Ty (..))
import TypeChecker
import Types

data ContextV :: forall n. Ctx n -> Type where
  NewV :: ContextV VNil
  WrapV :: Val a -> ContextV e -> ContextV (a :> e)

-- deriving instance Show (ContextV ctx)

lookupV :: DBIndex ctx ty -> ContextV ctx -> Val ty
lookupV ZeroDB (WrapV v _) = v
lookupV (SuccDB n) (WrapV _ cs) = lookupV n cs

data Val :: Ty -> Type where
  PrecV :: PR n -> Val (TyPrec n)
  ClosV :: ContextV e -> ExpTC (a :> e) b -> Val (a :-> b)
  VecV :: Vec n (Val a) -> Val (TyList n a)
  NatV :: !Integer -> Val TyNat
  RunPR :: ArithFun n -> Val (TyList n TyNat :-> TyNat)

-- deriving instance Show (Val ty)

expToVal :: forall (n :: Nat) (c :: Ctx n) (t :: Ty). ContextV c -> ExpTC c t -> Val t
expToVal _ (NatTC n) = NatV n
expToVal _ NilTC = VecV VNil
expToVal e (ConsTC x xs) = case expToVal e xs of VecV vec -> VecV $ expToVal e x :> vec
expToVal ctxV (LamTC e) = ClosV ctxV e
expToVal ctxV (AppTC f x) = case expToVal ctxV f of
  ClosV cV exp ->
    let xV = expToVal ctxV x
        newCV = WrapV xV cV
     in expToVal newCV exp
  RunPR pr -> case expToVal ctxV x of
    VecV vec -> NatV $ pr (fmap (\(NatV n) -> n) vec)
expToVal e (LetTC x y) = expToVal (WrapV (expToVal e x) e) y
expToVal e (VarTC n) = lookupV n e
expToVal e (RunPrecTC pr) = case expToVal e pr of PrecV pr' -> RunPR $ evalSafePr pr'
expToVal _ (BasePRecTC pr) = PrecV pr
expToVal e (PRecTC g h) = case (expToVal e g, expToVal e h) of (PrecV g', PrecV h') -> PrecV $ PRec g' h'
expToVal e (CompTC f gs) = case (expToVal e f, expToVal e gs) of (PrecV f, VecV gs') -> PrecV $ Comp f (fmap (\(PrecV pr) -> pr) gs')

prettyVecVal' :: Monad m => (Val a -> m (Doc ann)) -> Val (TyList n a) -> m (Doc ann)
prettyVecVal' f (VecV v) = encloseSep lbracket rbracket comma <$> mapM f (toList v)

prettyVecVal :: (Val a -> Doc ann) -> Val (TyList n a) -> Doc ann
prettyVecVal f xs = runIdentity (prettyVecVal' (return . f) xs)

tryToPrettyVal :: STy a -> Val a -> Maybe (Doc ann)
tryToPrettyVal STyNat (NatV n) = return $ pretty n
tryToPrettyVal (STyList _ ty) xs = prettyVecVal' (tryToPrettyVal ty) xs
tryToPrettyVal (_ ::-> _) _ = Nothing
tryToPrettyVal (STyPrec na) (PrecV pr) = return $ prettyPR na pr

prettyResAndTypeVal :: MonadError String m => STy a -> Val a -> m (Doc ann)
prettyResAndTypeVal ty res = do
  s <- prettyResVal ty res
  return $ line <> s <> line <> "has type:" <+> pretty ty <> line

prettyResVal :: MonadError String m => STy a -> Val a -> m (Doc ann)
prettyResVal ty res = case tryToPrettyVal ty res of
  Nothing ->
    throwError $
      "cant show function of type: "
        ++ show (pretty ty)
        ++ " \n"
  Just s -> return s
