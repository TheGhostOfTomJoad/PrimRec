{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Lib.HReader (hlocal) where

import Control.Monad.RWS
import Control.Monad.Reader
import Data.Kind

-- this is not my code
-- its from this repo: https://gitlab.com/goldfirere/stitch/

class Monad m => MonadHReader r1 m | m -> r1 where
  -- | Update the environment to a new type
  type SetEnv r2 m :: Type -> Type

  -- | Compute with a local environment, possibly of a different
  -- type than the outer environment
  hlocal :: (Monad (SetEnv r2 m)) => (r1 -> r2) -> SetEnv r2 m a -> m a

instance Monad m => MonadHReader r1 (ReaderT r1 m) where
  type SetEnv r2 (ReaderT r1 m) = ReaderT r2 m
  hlocal f action = ReaderT $ runReaderT action . f

instance (Monoid w, Monad m) => MonadHReader r1 (RWST r1 w s m) where
  type SetEnv r2 (RWST r1 w s m) = RWST r2 w s m
  hlocal f action = RWST $ runRWST action . f
