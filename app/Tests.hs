{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Tests where

import Control.Monad.Extra
import Data.Data
import qualified Language.Haskell.Interpreter as Hint
import Lib.SNat
import Lib.Vector (ArithFun, Curry, Vec (..), uncurry')
import Prettyprinter
import Test.QuickCheck
import Types

eval ::
  forall t.
  Typeable t =>
  String ->
  IO (Either Hint.InterpreterError t)
eval s = Hint.runInterpreter $ do
  Hint.setImportsQ
    [ ("Prelude", Nothing),
      ("Math.NumberTheory.Primes.Testing", Just "T"),
      ("Math.NumberTheory.Primes", Just "P"),
      ("Math.NumberTheory.Primes.Counting", Just "C")
    ]
  Hint.interpret s (Hint.as :: t)

replaceWithFasterPR :: SNat n -> PR n -> String -> IO (Maybe (PR n))
replaceWithFasterPR sn = withTypeableArbitrary sn replaceWithFasterPRHelper

prettyErr :: Hint.InterpreterError -> Doc ann
prettyErr err = case err of
  Hint.UnknownError str -> pretty str
  Hint.WontCompile ghcError -> vsep $ map (\(Hint.GhcError s) -> pretty s) ghcError
  Hint.NotAllowed str -> pretty str
  Hint.GhcException str -> pretty str

withTypeableArbitrary :: SNat n -> ((Typeable (Curry n), Arbitrary (Vec n Integer)) => r) -> r
withTypeableArbitrary SZ r = r
withTypeableArbitrary (Sy n) r = withTypeableArbitrary n r

replaceWithFasterPRHelper ::
  (Typeable (Curry n), Arbitrary (Vec n Integer)) =>
  PR n ->
  String ->
  IO (Maybe (PR n))
replaceWithFasterPRHelper pr hsCode = do
  maybeFun <- eval hsCode
  case maybeFun of
    Left err -> do
      print (prettyErr err)
      return Nothing
    Right fun -> convertIfEqual (uncurry' fun) pr

convertIfEqual :: Arbitrary (Vec n Integer) => ArithFun n -> PR n -> IO (Maybe (PR n))
convertIfEqual f pr = whenMaybeM (comparePRToArith f pr) (return $ PR f)

comparePRToArith :: Arbitrary (Vec n Integer) => ArithFun n -> PR n -> IO Bool
comparePRToArith f pr =
  isSuccess
    <$> quickCheckWithResult
      stdArgs {maxSuccess = 10, maxDiscardRatio = 1}
      (\v -> unPR pr v == f v)
