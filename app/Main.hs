{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Main (main) where

import Control.Monad.Except
import Data.Either.Extra
import qualified Data.Text.Internal.Lazy as L
import qualified Data.Text.Lazy.IO as L
import HOAS
import Interpreter ()
import Lib.HList
import Lib.Nat
import Lib.Vector
import Parser (runParseExp)
import Pretty
import Prettyprinter (Doc)
import REPL
  ( ARes (..),
    evalExpN,
    evalExpNCPS,
    repl,
  )
import ScopeCheck
import Syntax
import TypeChecker
import Types

main :: IO ()
main = repl

evalClosed :: ExpN -> Either (Doc ann) ARes
evalClosed = evalExpN VNil HNil HNil

evalClosedCPS ::
  ExpN ->
  (forall (a :: Ty) b. STy a -> Eval a -> Either (Doc ann) b) ->
  Either (Doc ann) b
evalClosedCPS = evalExpNCPS VNil HNil HNil

parseInterpret :: L.Text -> Either String String
parseInterpret code = do
  expN <- mapLeft show $ runParseExp code
  (ARes sTy a) <- mapLeft show $ evalClosed expN
  show <$> mapLeft show (runExcept (prettyResAndType sTy a))

main2 :: IO ()
main2 = do
  putStrLn "\nPrimRec"
  putStrLn "\nfilename:"
  fileName <- getLine
  code <- L.readFile fileName
  print $ fromEither $ parseInterpret code

evalExpN' ::
  forall (n :: Nat) (env :: Ctx n) ann.
  Vec n String ->
  STyContext env ->
  HoasContext env ->
  ExpN ->
  Either (Doc ann) ARes
evalExpN' varNames tyContext hoasContext expN = do
  expSC <- scopeCheck varNames expN
  AExpTC sTy expTC <- typeCheck tyContext expSC
  let expH = dBToHoas hoasContext expTC
  return $ ARes sTy (eval expH)

evalClosed' :: ExpN -> Either (Doc ann) ARes
evalClosed' = evalExpN' VNil HNil HNil

parseInterpret' :: L.Text -> Either String String
parseInterpret' code = do
  expN <- mapLeft show $ runParseExp code
  (ARes sTy a) <- mapLeft show $ evalClosed' expN
  show <$> mapLeft show (runExcept (prettyResAndType sTy a))

main3 :: IO ()
main3 = do
  putStrLn "\nPrimRec"
  putStrLn "\nfilename:"
  fileName <- getLine
  code <- L.readFile fileName
  putStrLn $ fromEither $ parseInterpret' code
