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
import Syntax
import Types

-- the function main2 evaluates only closed terms
main :: IO ()
main = repl

evalClosed :: ExpN -> Either (Doc ann) ARes
evalClosed = evalExpN VNil EmptySTyC EmptyVC

evalClosedCPS ::
  ExpN ->
  (forall (a :: Ty) b. STy a -> Eval a -> Either (Doc ann) b) ->
  Either (Doc ann) b
evalClosedCPS = evalExpNCPS VNil EmptySTyC EmptyVC

parseInterpret :: L.Text -> Either String ARes
parseInterpret code = do
  expN <- mapLeft show $ runParseExp code
  mapLeft show $ evalClosed expN

main2 :: IO ()
main2 = do
  putStrLn "\nPrimRec"
  putStrLn "\nfilename:"
  fileName <- getLine
  code <- L.readFile fileName
  case parseInterpret code of
    Right (ARes sTy a) ->
      putStrLn $ either show show $ runExcept (prettyResAndType sTy a)
    Left err -> print err
