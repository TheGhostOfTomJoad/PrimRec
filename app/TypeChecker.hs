{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module TypeChecker (ExpTC (..), AExpTC (..), typeCheck', typeCheck) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Data
import Data.Either.Utils
import Data.Kind (Type)
import Data.Type.Equality
import GHC.Natural (Natural)
import Lib.HList
import Lib.HReader
import Lib.Nat
import Lib.Types
import Prettyprinter
import ScopeCheck
import Syntax (Ty (..))

data AExpTC :: [Ty] -> Type where
  AExpTC :: STy a -> ExpTC e a -> AExpTC e

data ExpTC :: [Ty] -> Ty -> Type where
  LetTC :: ExpTC e a -> ExpTC (a : e) b -> ExpTC e b
  VarTC :: Index e a -> ExpTC e a
  LamTC :: ExpTC (a : e) b -> ExpTC e (a :-> b)
  AppTC :: ExpTC e (a :-> b) -> ExpTC e a -> ExpTC e b
  NatTC :: Natural -> ExpTC e TyNat
  SuccTC :: ExpTC e (TyNat :-> TyNat)
  PRecTC :: ExpTC e (t :-> (TyNat :-> t)) -> ExpTC e (t :-> (TyNat :-> t))

-- PRecTC :: ExpTC e (t :-> (TyNat :-> t)) -> ExpTC e (t) -> ExpTC e (TyNat) ->ExpTC e (t)

deriving instance (Show (ExpTC env a))

instance Pretty (ExpTC env a) where
  pretty (LetTC _ _) = error ""
  pretty (VarTC v) = pretty v
  pretty (LamTC e) = "\\" <+> pretty e
  pretty (AppTC f x) = parens (pretty f) <+> parens (pretty x)
  pretty (NatTC n) = pretty n
  pretty SuccTC = "S"
  pretty (PRecTC f) = "P" <+> parens (pretty f)

type TypeCheckM n e ann a = CheckM n (STyContext e n) ann a

tCBind :: STy ty -> TypeCheckM (S n) (ty : e) a ann -> TypeCheckM n e a ann
tCBind bound_var = hlocal (bound_var `HCons`)

typeCheck :: forall (n :: Nat) e ann. STyContext e n -> ExpSC n -> Either (Doc ann) (AExpTC e)
typeCheck context exp = runExcept $ runReaderT (tCHelper exp) context

typeCheck' :: ExpSC 'Z -> Either (Doc ann) (AExpTC '[])
typeCheck' = typeCheck HNil

testEqualityError :: (MonadError e m, TestEquality f) => e -> f a -> f b -> m (a :~: b)
testEqualityError s e1 e2 = maybeToEither s $ testEquality e1 e2

tCHelper :: ExpSC n -> TypeCheckM n e ann (AExpTC e)
tCHelper SuccSC = return $ AExpTC (STyNat ::-> STyNat) SuccTC
tCHelper (LetSC t1 t2) = do
  (AExpTC ty1 f) <- tCHelper t1
  (AExpTC ty2 g) <- tCBind ty1 $ tCHelper t2
  return $ AExpTC ty2 (LetTC f g)
tCHelper (VarSC n) = do
  e <- ask
  finToIndexCPS n e (\db st -> return $ AExpTC st $ VarTC db)
tCHelper (AppSC f x) = do
  AExpTC tyF fC <- tCHelper f
  AExpTC tyX xC <- tCHelper x
  case tyF of
    (tyFa ::-> tyFb) ->
      do
        Refl <- testEqualityError "The Argument of the function application has the wrong type" tyFa tyX
        return $ AExpTC tyFb (AppTC fC xC)
    _ -> throwError "In a Function application, the first argument must have a function type"
tCHelper (LamSC ty1 t) = do
  AExpTC ty2 fexp1 <- tCBind ty1 $ tCHelper t
  return $ AExpTC (ty1 ::-> ty2) (LamTC fexp1)
tCHelper (NatSC n) = return $ AExpTC STyNat (NatTC n)
tCHelper (PRecSC f) = do
  AExpTC sTyF fTC <- tCHelper f
  case sTyF of
    (sTy ::-> (STyNat ::-> sTy')) -> do
      Refl <- testEqualityError "primtive recursion  can only be used with functions where the fist argument and the result of the function must have the same type" sTy sTy'
      return $ AExpTC sTyF (PRecTC fTC)
    _ -> throwError "primtive recursion  can only be used with functions with at leat to arguments. The second argument must be of type Nat"
