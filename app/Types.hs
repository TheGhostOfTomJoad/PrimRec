{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Types (ATy (ATy), STy (..), Ctx, tyToSTy, Eval, STyContext, ValContext, tyToStyCPS, ID (..)) where

import Data.Kind (Type)
import Data.Type.Equality
import Lib.HList
import Lib.Vector
import Numeric.Natural
import Prettyprinter
import Syntax
import Test.QuickCheck ()

type family Eval (t :: Ty) = res | res -> t where
  Eval TyNat = Natural
  Eval (a :-> b) = Eval a -> Eval b

tyToSTy :: Ty -> ATy
tyToSTy TyNat = ATy STyNat
tyToSTy (t1 :-> t2) = case (tyToSTy t1, tyToSTy t2) of
  (ATy t1, ATy t2) -> ATy $ t1 ::-> t2

tyToStyCPS :: Ty -> (forall a. STy a -> b) -> b
tyToStyCPS TyNat g = g STyNat
tyToStyCPS (t1 :-> t2) g = tyToStyCPS t1 (\st1 -> tyToStyCPS t2 (\st2 -> g $ st1 ::-> st2))

data STy :: Ty -> Type where
  STyNat :: STy TyNat
  (::->) :: STy a -> STy b -> STy (a :-> b)

deriving instance Show (STy a)

instance Pretty (STy a) where
  pretty = prettyTy

isArrow :: STy a -> Bool
isArrow (_ ::-> _) = True
isArrow _ = False

-- https://github.com/sdiehl/write-you-a-haskell/blob/master/chapter7/poly/src/Pretty.hs
parensIf :: Pretty a => (a -> Bool) -> a -> Doc ann
parensIf f x = if f x then parens (pretty x) else pretty x

prettyTy :: STy a -> Doc ann
prettyTy STyNat = "Nat"
prettyTy (a ::-> b) = parensIf isArrow a <+> "->" <+> prettyTy b

data ATy :: Type where
  ATy :: STy ty -> ATy

instance TestEquality STy where
  testEquality STyNat STyNat = Just Refl
  testEquality (a ::-> b) (c ::-> d) = do
    Refl <- testEquality a c
    Refl <- testEquality b d
    return Refl
  testEquality _ _ = Nothing

type Ctx n = Vec n Ty

type STyContext e = HList STy e

newtype ID a = ID {unID :: Eval a}

instance Pretty (ID TyNat) where
  pretty (ID n) = pretty n

instance Pretty (ID (a :-> b)) where
  pretty (ID _) = "<function>"

type ValContext e = HList ID e
