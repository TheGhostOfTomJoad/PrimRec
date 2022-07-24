{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty (prettyRes, prettyPR, prettyResAndType) where

import Control.Monad.Except
import Lib.PrettyHelpers
import Lib.SNat
import Lib.Vector
import Precs
import Prettyprinter
import Types

prettyPR :: SNat n -> PR n -> Doc ann
prettyPR na ConstZero = "Z" <+> pretty na
prettyPR _ Succ = "S"
prettyPR na (Proj fin) = "Pi" <+> pretty na <+> pretty fin
prettyPR (Sy na) (PRec g f) = "P" <+> parens (prettyPR na g) <+> parens (prettyPR (Sy (Sy na)) f)
prettyPR na (Comp f gs) = "C" <+> parens (prettyPR (len gs) f) <+> prettyVec (prettyPR na) gs
prettyPR na (InBuilt _ pr) = prettyPR na pr

tryToPretty :: STy a -> Eval a -> Maybe (Doc ann)
tryToPretty STyNat n = return $ pretty n
tryToPretty (STyList _ ty) xs = prettyVec' (tryToPretty ty) xs
tryToPretty (_ ::-> _) _ = Nothing
tryToPretty (STyPrec na) pr = return $ prettyPR na pr

prettyRes :: MonadError (Doc ann) m => STy a -> Eval a -> m (Doc ann)
prettyRes = prettyResHelper tryToPretty

prettyResAndType :: MonadError (Doc ann) m => STy a -> Eval a -> m (Doc ann)
prettyResAndType = prettyResAndTypeHelper tryToPretty
