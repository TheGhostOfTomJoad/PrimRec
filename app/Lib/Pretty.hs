{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Lib.Pretty (prettyRes, prettyResAndType) where

import Control.Monad.Except
import Lib.Types
import Prettyprinter

tryToPretty :: STy a -> Eval a -> Maybe (Doc ann)
tryToPretty STyNat n = return $ pretty n
tryToPretty (_ ::-> _) _ = Nothing

prettyResAndType :: MonadError (Doc ann) m => STy a -> Eval a -> m (Doc ann)
prettyResAndType ty res = do
  s <- prettyRes ty res
  return $ line <> s <> line <> "has type:" <+> pretty ty <> line

prettyRes :: MonadError (Doc ann) m => STy a -> Eval a -> m (Doc ann)
prettyRes ty res = case tryToPretty ty res of
  Nothing ->
    throwError $
      "cant show function of type: "
        <+> pretty ty
          <> line
  Just s -> return s
