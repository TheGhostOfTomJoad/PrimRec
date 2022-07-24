{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Control.Monad.Except
import Data.Either.Extra (mapLeft)
import qualified Data.Text.Internal.Lazy as L
import qualified Data.Text.Lazy.IO as L
import Lib.Vector
import Parser
import Pretty (prettyResAndType)
import Prettyprinter
import REPL
import ScopeCheck
import Types

main :: IO ()
main = repl

evalClosed :: ExpN' -> Either (Doc ann) ARes
evalClosed = evalExpN VNil EmptySTyC EmptyVC

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
