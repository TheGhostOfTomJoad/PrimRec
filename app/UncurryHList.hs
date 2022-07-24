{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module UncurryHList (UncurryH, HList', TyArgs, withConstraints, uncurryH) where

import Data.Data
import Data.Kind
import Lib.Types
import Prettyprinter
import Syntax (Ty (..))
import Test.QuickCheck

type TyArgs :: Ty -> [Ty]
type family TyArgs ty where
  TyArgs TyNat = '[]
  TyArgs (a :-> b) = a : TyArgs b

data HList' :: forall. (k -> Type) -> [k] -> Type where
  HNil' :: HList' f '[]
  HCons' :: f x -> HList' f xs -> HList' f (x : xs)

instance Pretty (HList' ID '[]) where
  pretty HNil' = ""

instance (Pretty (HList' ID xs), Pretty (ID x)) => Pretty (HList' ID (x : xs)) where
  pretty (HCons' y@(ID _) xs) = pretty y <+> pretty xs

instance (Pretty (HList' ID xs)) => Show (HList' ID xs) where
  show = show . pretty

instance Arbitrary (HList' ID '[]) where
  arbitrary = return HNil'

instance (Arbitrary (HList' ID xs), Arbitrary (Eval x)) => Arbitrary (HList' ID (x : xs)) where
  arbitrary = do
    x <- arbitrary
    HCons' (ID x) <$> arbitrary

class UncurryH ty where
  uncurryH :: Eval ty -> HList' ID (TyArgs ty) -> Eval TyNat

instance UncurryH TyNat where
  uncurryH ev HNil' = ev

instance (UncurryH b) => UncurryH (a :-> b) where
  uncurryH ev (HCons' (ID x) xs) = uncurryH (ev x) xs

withConstraints ::
  forall a r.
  STy a ->
  ( ( Typeable (Eval a),
      Pretty (HList' ID (TyArgs a)),
      UncurryH a,
      Pretty (ID a),
      Arbitrary (Eval a),
      CoArbitrary (Eval a),
      Arbitrary (HList' ID (TyArgs a))
    ) =>
    r
  ) ->
  r
withConstraints STyNat r = r
withConstraints (st ::-> st') r = withConstraints st' $ withConstraints st r
