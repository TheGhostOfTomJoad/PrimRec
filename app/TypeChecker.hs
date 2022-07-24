{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module TypeChecker (ExpTC (..), AExpTC (..), typeCheck', typeCheck) where

--
--
--
--
--
import Control.Monad.Except
import Control.Monad.Reader
import Data.Data
import Data.Either.Utils
import Data.Kind (Type)
import Data.Type.Equality
import Lib.Fin
import Lib.HReader
import Lib.Nat
import Lib.SNat
import Lib.Vector
import Precs
import Prettyprinter
import ScopeCheck
import Syntax (Ty (..))
import Types

data AExpTC :: forall n. Ctx n -> Type where
  AExpTC :: STy a -> ExpTC e a -> AExpTC e

data ExpTC :: forall n. Ctx n -> Ty -> Type where
  NatTC :: Integer -> ExpTC env TyNat
  LetTC :: ExpTC env a -> ExpTC (a :> env) b -> ExpTC env b
  LamTC :: ExpTC (a :> env) b -> ExpTC env (a :-> b)
  VarTC :: DBIndex env a -> ExpTC env a
  AppTC :: ExpTC env (a :-> b) -> ExpTC env a -> ExpTC env b
  NilTC :: ExpTC env (TyList Z a)
  ConsTC ::
    ExpTC env a ->
    ExpTC env (TyList n a) ->
    ExpTC env (TyList (S n) a)
  BasePRecTC :: PR n -> ExpTC env (TyPrec n)
  CompTC ::
    ExpTC env (TyPrec n) ->
    ExpTC env (TyList n (TyPrec m)) ->
    ExpTC env (TyPrec m)
  PRecTC ::
    ExpTC env (TyPrec n) ->
    ExpTC env (TyPrec (S (S n))) ->
    ExpTC env (TyPrec (S n))
  RunPrecTC :: ExpTC env (TyPrec n) -> ExpTC env (TyList n TyNat :-> TyNat)

-- deriving instance Show (ExpTC ctx ty)

type TypeCheckM n env ann a = CheckM n (STyContext (env :: Ctx n)) ann a

tCBind ::
  STy ty ->
  TypeCheckM (S n) (ty :> env) a ann ->
  TypeCheckM n env a ann
tCBind bound_var = hlocal (bound_var `ExtendSTyC`)

typeCheck ::
  forall (n :: Nat) (env :: Ctx n) ann.
  STyContext env ->
  ExpSC n ->
  Either (Doc ann) (AExpTC env)
typeCheck context exp = runExcept $ runReaderT (tCHelper exp) context

typeCheck' :: ExpSC 'Z -> Either (Doc ann) (AExpTC 'VNil)
typeCheck' = typeCheck EmptySTyC

convertDB :: Fin n -> STyContext (env :: Ctx n) -> ADBIndex env
convertDB FZero (ExtendSTyC sTy _) = ADBIndex sTy ZeroDB
-- convertDB n        EmptySTyC            = error "unbound variable"
convertDB (FSuc n) (ExtendSTyC _ env) = case convertDB n env of
  ADBIndex sTy db -> ADBIndex sTy $ SuccDB db

convertDbCPS ::
  Fin n ->
  STyContext (env :: Ctx n) ->
  (forall a. DBIndex env a -> STy a -> b) ->
  b
convertDbCPS FZero (ExtendSTyC sTy _) g = g ZeroDB sTy
-- -- convertDB n        EmptySTyC            = error "unbound variable"
convertDbCPS (FSuc n) (ExtendSTyC _ env) g = convertDbCPS n env (g . SuccDB)

testEqualityError ::
  (MonadError err m, TestEquality f) =>
  err ->
  f a ->
  f b ->
  m (a :~: b)
testEqualityError errM e1 e2 = maybeToEither errM $ testEquality e1 e2

tCHelper :: ExpSC n -> TypeCheckM n env ann (AExpTC env)
tCHelper (NatSC n) = return $ AExpTC STyNat (NatTC n)
tCHelper (LetSC t1 t2) = do
  (AExpTC ty1 f) <- tCHelper t1
  (AExpTC ty2 g) <- tCBind ty1 $ tCHelper t2
  return $ AExpTC ty2 (LetTC f g)
tCHelper (LamSC sTyA t) = do
  AExpTC sTyB tC <- tCBind sTyA $ tCHelper t
  return $ AExpTC (sTyA ::-> sTyB) (LamTC tC)
tCHelper (VarSC n) = do
  env <- ask
  ADBIndex ty db <- return $ convertDB n env
  return $ AExpTC ty (VarTC db)
tCHelper (VarSC n) = do
  env <- ask
  convertDbCPS n env (\db st -> return $ AExpTC st $ VarTC db)
tCHelper (AppSC f x) = do
  AExpTC tyF fC <- tCHelper f
  AExpTC tyX xC <- tCHelper x
  case tyF of
    (tyFa ::-> tyFb) ->
      do
        Refl <- testEqualityError "The argument of the function application has the wrong type" tyFa tyX
        return $ AExpTC tyFb (AppTC fC xC)
    _ -> throwError "In a Function application, the first argument must have a function type"
tCHelper (NilSC Nothing) = throwError "Unannotated empty vector"
tCHelper (NilSC (Just ty)) = return $ AExpTC (STyList SZ ty) NilTC
tCHelper (ConsSC x (NilSC Nothing)) = do
  AExpTC tyX x' <- tCHelper x
  return $ AExpTC (STyList (Sy SZ) tyX) (ConsTC x' NilTC)
tCHelper (ConsSC x xs) = do
  AExpTC tyX xC <- tCHelper x
  AExpTC tyXs xsC <- tCHelper xs
  case tyXs of
    (STyList n tyY) -> do
      Refl <-
        testEqualityError
          "Vectors can only have elements of one type"
          tyX
          tyY
      return $ AExpTC (STyList (Sy n) tyX) (ConsTC xC xsC)
    _ ->
      throwError
        "Cons can only be used with vectors and elements of the right type"
tCHelper (BasePRecSC sn pr) = return $ AExpTC (STyPrec sn) (BasePRecTC pr)
tCHelper (PRecSC g f) = do
  AExpTC tyG gC <- tCHelper g
  case tyG of
    (STyPrec arityG) -> do
      AExpTC tyF fC <- tCHelper f
      case tyF of
        (STyPrec arityF) -> case arityF of
          (Sy (Sy n)) -> do
            Refl <- testEqualityError "Mismatching aritys in P" n arityG
            return $ AExpTC (STyPrec (Sy arityG)) (PRecTC gC fC)
          _ ->
            throwError
              "The second argument of P must have an arity, that is at least two"
        _ ->
          throwError
            "The second argument of P must be a primitive recursive function"
    _ ->
      throwError
        "The first argument of P must be a primitive recursive function"
tCHelper (CompSC f gs) = do
  AExpTC tyF fC <- tCHelper f
  case tyF of
    (STyPrec arityF) -> do
      (AExpTC tyGs gsC) <- tCHelper gs
      case tyGs of
        (STyList lenGs tyGs@((STyPrec _))) -> do
          Refl <- testEqualityError "The length of the list and the arity of the function must be equal in a composition" lenGs arityF
          return $ AExpTC tyGs (CompTC fC gsC)
        _ -> throwError "The second argument of a Composition must be a vector of primitve recursive functions"
    _ -> throwError "The first argument of a Composition must be a primitiv recursive function"
tCHelper (RunPrekSC mP) = do
  AExpTC tyP pC <- tCHelper mP
  case tyP of
    STyPrec n -> return $ AExpTC (STyList n STyNat ::-> STyNat) (RunPrecTC pC)
    _ -> throwError "You can only use run with primitiv recursive functions"

-- typeCheck :: STyContext (e :: Ctx n) -> ExpSC n -> Maybe (AExpTC e)
-- typeCheck _ SuccSC = return $ AExpTC (STyPrec (Sy SZ)) SuccTC
-- typeCheck _ (ConstZeroSC na) = return $ AExpTC (STyPrec na) ConstZeroTC
-- typeCheck _ (ProjSC fin na) = return $ AExpTC (STyPrec na) (ProjTC fin)
-- typeCheck e (PRecSC mg mf) = do
--   AExpTC (STyPrec n) g <- typeCheck e mg
--   AExpTC (STyPrec (Sy (Sy m))) f <- typeCheck e mf
--   Refl <- testEquality n m
--   return $ AExpTC (STyPrec (Sy n)) (PRecTC g f)
-- typeCheck e (CompSC f gs) = do
--   AExpTC (STyPrec arityF) fC <- typeCheck e f
--   (AExpTC (STyList lenGs tyGs@((STyPrec _))) gsC) <- typeCheck e gs
--   Refl <- testEquality lenGs arityF
--   return $ AExpTC tyGs (CompTC fC gsC)
-- typeCheck e (LetSC t1 t2) = do
--   (AExpTC ty1 f) <- typeCheck e t1
--   (AExpTC ty2 g) <- typeCheck (ExtendSTyC ty1 e) t2
--   return $ AExpTC ty2 (LetTC f g)
-- typeCheck e (VarSC n) = do
--   ADBIndex ty db <- return $ convertDB n e
--   return $ AExpTC ty (VarTC db)
-- typeCheck e (AppSC t1 t2) = do
--   AExpTC (tyA ::-> tyB) t1C <- typeCheck e t1
--   AExpTC tyC t2C <- typeCheck e t2
--   Refl <- testEquality tyA tyC
--   return $ AExpTC tyB (AppTC t1C t2C)
-- typeCheck e (LamSC ty1 t) = do
--   AExpTC ty2 fexp1 <- typeCheck (ExtendSTyC ty1 e) t
--   return $ AExpTC (ty1 ::-> ty2) (LamTC fexp1)
-- typeCheck _ (NilSC Nothing) = Nothing
-- typeCheck _ (NilSC (Just ty)) = return $ AExpTC (STyList SZ ty) NilTC
-- typeCheck e (ConsSC x (NilSC Nothing)) = do
--   AExpTC tyX x' <- typeCheck e x
--   return $ AExpTC (STyList (Sy SZ) tyX) (ConsTC x' NilTC)
-- typeCheck e (ConsSC x xs) = do
--   AExpTC tyX x' <- typeCheck e x
--   AExpTC (STyList n tyXs) xs' <- typeCheck e xs
--   Refl <- testEquality tyX tyXs
--   return $ AExpTC (STyList (Sy n) tyX) (ConsTC x' xs')
-- typeCheck _ (NatSC n) = return $ AExpTC STyNat (NatTC n)
-- typeCheck e (RunPrekSC p) = do
--   AExpTC (STyPrec n) expr <- typeCheck e p
--   return $ AExpTC (STyList n STyNat ::-> STyNat) (RunPrecTC expr)
