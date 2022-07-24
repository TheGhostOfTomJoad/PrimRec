{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Types (ATy (ATy), STy (..), Ctx, tyToSTy, DBIndex (..), STyContext (..), ADBIndex (ADBIndex), Eval, ValContext (..), lookupVar, tyToStyCPS) where

-- import Converter3 (ATy (ATy), Ty,STy, tyToSTy )

import Data.Kind (Type)
import Data.Type.Equality
import Lib.SNat
import qualified Lib.SNat as SNat
import Lib.Vector
import Precs
import Prettyprinter
import Syntax

type family Eval (t :: Ty) where
  Eval TyNat = Integer
  Eval (a :-> b) = Eval a -> Eval b
  Eval (TyList n ty) = Vec n (Eval ty)
  Eval (TyPrec n) = PR n

tyToSTy :: Ty -> ATy
tyToSTy TyNat = ATy STyNat
tyToSTy (t1 :-> t2) = case (tyToSTy t1, tyToSTy t2) of
  (ATy t1, ATy t2) -> ATy $ t1 ::-> t2
tyToSTy (TyList n ty) = case (SNat.fromNat n, tyToSTy ty) of
  (ASNat sn, ATy sTy) -> ATy (STyList sn sTy)
tyToSTy (TyPrec n) = case SNat.fromNat n of
  ASNat na -> ATy (STyPrec na)

tyToStyCPS :: Ty -> (forall a. STy a -> b) -> b
tyToStyCPS TyNat g = g STyNat
tyToStyCPS (t1 :-> t2) g =
  tyToStyCPS
    t1
    ( \st1 ->
        tyToStyCPS
          t2
          (\st2 -> g $ st1 ::-> st2)
    )
tyToStyCPS (TyList n ty) g =
  SNat.fromNatCPS
    n
    (\sn -> tyToStyCPS ty (g . STyList sn))
tyToStyCPS (TyPrec n) g = SNat.fromNatCPS n (g . STyPrec)

data STy :: Ty -> Type where
  STyNat :: STy TyNat
  (::->) :: STy a -> STy b -> STy (a :-> b)
  STyList :: SNat n -> STy a -> STy (TyList n a)
  STyPrec :: SNat n -> STy (TyPrec n)

deriving instance Show (STy a)

instance Pretty (STy a) where
  pretty = prettyTy

isArrow :: STy a -> Bool
isArrow (_ ::-> _) = True
isArrow _ = False

isNat :: STy a -> Bool
isNat STyNat = True
isNat _ = False

-- https://github.com/sdiehl/write-you-a-haskell/blob/master/chapter7/poly/src/Pretty.hs
parensIf :: Pretty a => (a -> Bool) -> a -> Doc ann
parensIf f x = if f x then parens (pretty x) else pretty x

prettyTy :: STy a -> Doc ann
prettyTy STyNat = "Nat"
prettyTy (a ::-> b) = parensIf isArrow a <+> "->" <+> prettyTy b
prettyTy (STyList n a) = "Vec" <+> pretty n <+> parensIf (not . isNat) a
prettyTy (STyPrec n) = "PR" <+> pretty n

data ATy :: Type where
  ATy :: STy ty -> ATy

instance TestEquality STy where
  testEquality STyNat STyNat = Just Refl
  testEquality (a ::-> b) (c ::-> d) = do
    Refl <- testEquality a c
    Refl <- testEquality b d
    return Refl
  testEquality (STyList n a) (STyList m b) = do
    Refl <- testEquality n m
    Refl <- testEquality a b
    return Refl
  testEquality (STyPrec n) (STyPrec m) = do
    Refl <- testEquality n m
    return Refl
  testEquality _ _ = Nothing

data DBIndex :: forall n. Ctx n -> Ty -> Type where
  ZeroDB :: DBIndex (a :> b) a
  SuccDB :: DBIndex e a -> DBIndex (b :> e) a

deriving instance Show (DBIndex ctx ty)

lookupVar :: DBIndex e a -> ValContext e -> Eval a
lookupVar ZeroDB (v `ExtendVC` _) = v
lookupVar (SuccDB db) (_ `ExtendVC` env) = lookupVar db env

data ADBIndex e where
  ADBIndex :: STy a -> DBIndex e a -> ADBIndex e

type Ctx n = Vec n Ty

data ValContext :: forall n. Ctx n -> Type where
  EmptyVC :: ValContext VNil
  ExtendVC :: Eval a -> ValContext e -> ValContext (a :> e)

data STyContext :: forall n. Ctx n -> Type where
  EmptySTyC :: STyContext VNil
  ExtendSTyC :: STy a -> STyContext e -> STyContext (a :> e)
