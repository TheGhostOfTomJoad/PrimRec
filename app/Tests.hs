{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests (replaceWithFasterPR) where

import Control.Monad.Cont ()
import Control.Monad.Extra
import Data.Data
import GHC.Natural ()
import qualified Language.Haskell.Interpreter as Hint
import Prettyprinter
import Test.QuickCheck
import Types
import UncurryHList

eval ::
  forall t.
  Typeable t =>
  String ->
  IO (Either Hint.InterpreterError t)
eval s = Hint.runInterpreter $ do
  Hint.setImportsQ
    [ ("Prelude", Nothing),
      ("GHC.Natural", Nothing),
      ("Math.NumberTheory.Primes.Testing", Just "T"),
      ("Math.NumberTheory.Primes", Just "P"),
      ("Math.NumberTheory.Primes.Counting", Just "C")
    ]
  Hint.interpret s (Hint.as :: t)

replaceWithFasterPR ::
  STy a ->
  Eval a ->
  String ->
  IO (Maybe (Eval a))
replaceWithFasterPR sn = withConstraints sn replaceWithFasterPRHelper

prettyErr :: Hint.InterpreterError -> Doc ann
prettyErr err = case err of
  Hint.UnknownError str -> pretty str
  Hint.WontCompile ghcError -> vsep $ map (\(Hint.GhcError s) -> pretty s) ghcError
  Hint.NotAllowed str -> pretty str
  Hint.GhcException str -> pretty str

replaceWithFasterPRHelper ::
  ( Typeable (Eval a),
    Arbitrary (HList' ID (TyArgs a)),
    Pretty (HList' ID (TyArgs a)),
    UncurryH a
  ) =>
  Eval a ->
  String ->
  IO (Maybe (Eval a))
replaceWithFasterPRHelper pr hsCode = do
  maybeFun <- eval hsCode
  case maybeFun of
    Left err -> do
      print (prettyErr err)
      return Nothing
    Right fun -> convertIfEqual fun pr

convertIfEqual ::
  ( Arbitrary (HList' ID (TyArgs a)),
    Pretty (HList' ID (TyArgs a)),
    UncurryH a
  ) =>
  Eval a ->
  Eval a ->
  IO (Maybe (Eval a))
convertIfEqual f pr = whenMaybeM (compareEval f pr) (return f)

compareEval ::
  ( Arbitrary (HList' ID (TyArgs a)),
    Pretty (HList' ID (TyArgs a)),
    UncurryH a
  ) =>
  Eval a ->
  Eval a ->
  IO Bool
compareEval f pr =
  isSuccess
    <$> quickCheckWithResult
      stdArgs {maxSuccess = 20, maxDiscardRatio = 1}
      (\v -> uncurryH pr v == uncurryH f v)

-- x :: IO Bool
-- x = compareEval (2 :: Natural) 2

-- y = compareEval ((+) :: Natural -> Natural -> Natural) (+)

-- z = compareEval (id :: Natural -> Natural) id

-- a = compareEval (const 0 :: Natural -> Natural) (const 0)

-- testArb :: IO (HList' ID '[ 'TyNat])
-- testArb = generate (arbitrary :: Gen (HList' ID '[TyNat]))

-- testArb' = generate (arbitrary :: Gen Natural)
