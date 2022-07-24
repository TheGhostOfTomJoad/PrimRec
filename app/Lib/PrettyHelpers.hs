{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib.PrettyHelpers where

import Control.Monad.Except
import Control.Monad.Identity
import Data.Foldable
import Lib.Vector
import Prettyprinter
import Types

prettyVec' :: Monad f => (a -> f (Doc ann)) -> Vec n a -> f (Doc ann)
prettyVec' f xs = encloseSep lbracket rbracket comma <$> mapM f (toList xs)

prettyVec :: (a -> Doc ann) -> Vec n a -> Doc ann
prettyVec f xs = runIdentity (prettyVec' (return . f) xs)

prettyResAndTypeHelper :: MonadError (Doc ann) m => (STy a -> Eval a -> Maybe (Doc ann)) -> STy a -> Eval a -> m (Doc ann)
prettyResAndTypeHelper f ty res = do
  s <- prettyResHelper f ty res
  return $ line <> s <> line <> "has type:" <+> pretty ty <> line

prettyResHelper :: MonadError (Doc ann) m => (STy a -> Eval a -> Maybe (Doc ann)) -> STy a -> Eval a -> m (Doc ann)
prettyResHelper f ty res = case f ty res of
  Nothing ->
    throwError $
      "cant show function of type: "
        <+> pretty ty
          <> line
  Just s -> return s
