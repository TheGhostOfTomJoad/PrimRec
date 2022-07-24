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
import Interpreter ()
import Lib.HList
import Lib.Pretty
import Lib.Types
import Lib.Vector
import Parser (runParseExp)
import Prettyprinter (Doc)
import REPL
  ( ARes (..),
    evalExpN,
    evalExpNCPS,
    repl,
  )
import Syntax

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
