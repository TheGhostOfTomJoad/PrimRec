{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module REPL where -- (evalExpN, repl, ARes (..)) where

import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Either.Extra (maybeToEither)
import Data.Foldable (Foldable (toList))
import Data.List (isPrefixOf, nub)
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as L
import Interpreter
import Lib.Nat
-- (STyContex (..), Ctx, Eval, STy (STyPrec), SContext (..))

import Lib.REPLHelper
import Lib.Vector
import Parser
import Pretty (prettyRes)
import Prettyprinter
import ScopeCheck
import Syntax
import System.Console.Repline
  ( CompleterStyle (Prefix),
    HaskelineT,
    WordCompleter,
    dontCrash,
    evalRepl,
    wordCompleter,
  )
import System.TimeIt
import Tests
import TypeCheck
import Types

data REPLState (env :: Ctx n) = REPLState {varNames :: Vec n String, tcContext :: STyContext env, context :: ValContext env}

data AREPLState where
  AREPLState :: REPLState ctx -> AREPLState

initReplState :: AREPLState
initReplState = AREPLState $ REPLState VNil EmptySTyC EmptyVC

type Repl a = HaskelineT (StateT AREPLState IO) a

data ARes where
  ARes :: STy a -> Eval a -> ARes

cmd :: L.Text -> Repl ()
cmd code = do
  tle <- hoistErr $ runParseTopLevelExp code
  execTLE tle

execTLE :: TopLevelExp ExpN' -> Repl ()
execTLE tle = do
  (AREPLState st) <- get
  case tle of
    TopLevelDec s expN -> execDecl s expN st
    TopLevelExp expN -> do
      (ARes sTy res) <- hoistErr' $ evalTop st expN
      liftIO $ putStrLn (either show show (prettyRes sTy res))
    Compare' hsCode expName -> compareToHaskell hsCode expName

execDecl :: String -> ExpN' -> REPLState env -> Repl ()
execDecl s expN st = do
  (ARes sTy res) <- hoistErr' $ withExcept (\x -> "in the declaration of" <+> pretty s <+> x) $ evalTop st expN
  updateState s sTy res st

evalExpN ::
  forall (n :: Nat) (env :: Ctx n) ann.
  Vec n String ->
  STyContext env ->
  ValContext env ->
  ExpN' ->
  Either (Doc ann) ARes
evalExpN varNames tcContext context expN = do
  expSC <- scopeCheck varNames expN
  (AExpTC sTy expTC) <- maybeToEither "" $ typeCheck tcContext expSC
  let res = evalSafe context expTC
   in return (ARes sTy res)

evalTop :: MonadError (Doc ann) m => REPLState env -> ExpN' -> m ARes
evalTop replState expN = liftEither $ evalExpN (varNames replState) (tcContext replState) (context replState) expN

updateStateHelper ::
  forall (n :: Nat) (a :: Ty) (e :: Ctx n).
  String ->
  STy a ->
  Eval a ->
  REPLState e ->
  REPLState (a ':> e)
updateStateHelper name sTy res replState =
  replState
    { varNames = name :> varNames replState,
      tcContext = sTy `ExtendSTyC` tcContext replState,
      context = res `ExtendVC` context replState
    }

updateState :: MonadState AREPLState m => String -> STy a -> Eval a -> REPLState ctx -> m ()
updateState name sTy res replState = put $ AREPLState (updateStateHelper name sTy res replState)

-- Completion

comp :: (Monad m, MonadState AREPLState m) => WordCompleter m
comp s = do
  AREPLState replState <- get
  return $ filter (isPrefixOf s) (nub $ toList (varNames replState))

opts :: [(String, String -> Repl ())]
opts =
  [ ("l", dontCrash . load . words),
    ("t", dontCrash . typeOf . words)
  ]

completer :: CompleterStyle (StateT AREPLState IO)
completer = Prefix (wordCompleter comp) defaultMatcher

repl :: IO ()
repl =
  flip evalStateT initReplState $
    evalRepl (const $ pure ">>> ") (timeIt . cmd . L.pack) opts (Just ':') Nothing completer ini final

load :: [String] -> Repl ()
load args = do
  contents <- liftIO $ L.readFile (unwords args)
  decls <- hoistErr $ pModule2 contents
  mapM_ execTLE decls

typeHelper :: [String] -> Repl ARes
typeHelper args = do
  let contents = unwords args
  AREPLState replState <- get
  expN <- hoistErr $ runParseExp (L.pack contents)
  hoistErr' $ evalTop replState expN

typeOf :: [String] -> Repl ()
typeOf args = do
  (ARes sTy _) <- typeHelper args
  liftIO $ print (pretty sTy)

compareToHaskell :: String -> String -> Repl ()
compareToHaskell hsCode varName = do
  AREPLState replState <- get
  expN <- hoistErr $ runParseVar (L.pack varName)
  (ARes sTy a) <- hoistErr' $ evalTop replState expN
  case sTy of
    STyPrec sn -> do
      maybeFasterPR <- liftIO $ replaceWithFasterPR sn a hsCode
      case maybeFasterPR of
        Nothing -> liftIO $ print $ show $ "error in the comparison of" <+> pretty hsCode <+> "with" <+> pretty varName
        Just newPR -> updateState varName sTy newPR replState
    _ -> liftIO $ putStrLn "this expression is not a primitive recursive function"
