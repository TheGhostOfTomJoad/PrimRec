{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Pretty (prettyRes, prettyResAndType) where

import Control.Monad.Except
import Lib.PrettyHelpers
import Prettyprinter
import Types

tryToPretty :: STy a -> Eval a -> Maybe (Doc ann)
tryToPretty STyNat n = return $ pretty n
tryToPretty (_ ::-> _) _ = Nothing

prettyRes :: MonadError (Doc ann) m => STy a -> Eval a -> m (Doc ann)
prettyRes = prettyResHelper tryToPretty

prettyResAndType :: MonadError (Doc ann) m => STy a -> Eval a -> m (Doc ann)
prettyResAndType = prettyResAndTypeHelper tryToPretty
