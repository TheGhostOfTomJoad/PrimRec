{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Sing where --https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Data/Singletons.hs

import Data.Kind
import Lib.Nat
import Lib.SNat
import qualified Lib.SNat as SNat
import Syntax (Ty)
import Types (STy, tyToStyCPS)

class SingKind k where
  -- It's a bit cleaner than the original approach to
  -- use a type family than a data family
  type Sing :: k -> Type

  -- | Convert unrefined data to a singleton, in continuation-passing
  -- style.
  toSing :: k -> (forall (a :: k). Sing a -> r) -> r

class SingI (a :: k) where
  sing :: Sing a

instance SingKind Nat where
  type Sing = SNat

  toSing = SNat.fromNatCPS

instance SingKind Ty where
  type Sing = STy

  toSing = Types.tyToStyCPS
