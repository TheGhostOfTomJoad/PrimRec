{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module REPL (evalExpN, repl, ARes (..), evalExpNCPS) where

import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Foldable (Foldable (toList))
import Data.Kind
import Data.List (isPrefixOf)
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as L
import Interpreter
import Lib.HList
import Lib.Nat
import Lib.Pretty (prettyRes)
import Lib.Types
import Lib.Vector
import Parser
import Prettyprinter
import REPLHelper
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
import TypeChecker

data REPLState (ctx :: [Ty]) n = REPLState
  { varNames :: Vec n String,
    sTyContext :: STyContext ctx n,
    valContext :: ValContext ctx n
  }

initReplState :: AREPLState
initReplState = AREPLState $ REPLState VNil HNil HNil

data AREPLState where
  AREPLState :: REPLState ctx n -> AREPLState

type Repl a = HaskelineT (StateT AREPLState IO) a

data ARes where
  ARes :: STy a -> Eval a -> ARes

cmd :: L.Text -> Repl ()
cmd code = do
  tle <- hoistErr $ runParseTopLevelExp code
  execTLE tle

execTLE :: TopLevelExp -> Repl ()
execTLE tle = do
  (AREPLState st) <- get
  case tle of
    TopLevelDec s expN -> execDecl s expN st
    TopLevelExp expN -> do
      (ARes sty res) <- hoistErr' $ evalTop st expN
      liftIO $ putStrLn (either show show (prettyRes sty res))
    Compare hsCode expName -> compareToHaskell hsCode expName

execDecl :: String -> ExpN -> REPLState e n -> Repl ()
execDecl s expN st = do
  (ARes sty res) <- hoistErr' $ withExcept (\x -> "in the declaration of" <+> pretty s <+> x) $ evalTop st expN
  updateState s sty res st

evalExpN ::
  forall (n :: Nat) (env :: [Ty]) ann.
  Vec n String ->
  STyContext env n ->
  ValContext env n ->
  ExpN ->
  Either (Doc ann) ARes
evalExpN varNames tyContext valContext expN = do
  expSC <- scopeCheck varNames expN
  AExpTC sTy expTC <- typeCheck tyContext expSC
  return $ ARes sTy (evalSafe valContext expTC)

evalExpNCPS ::
  forall (n :: Nat) (env :: [Ty]) ann b.
  Vec n String ->
  STyContext env n ->
  ValContext env n ->
  ExpN ->
  (forall a b. STy a -> Eval a -> Either (Doc ann) b) ->
  Either (Doc ann) b
evalExpNCPS varNames tyContext valContext expN g = do
  expSC <- scopeCheck varNames expN
  AExpTC sTy expTC <- typeCheck tyContext expSC
  g sTy (evalSafe valContext expTC)

evalTop :: forall (n :: Nat) (m :: Type -> Type) (ctx :: [Ty]) ann. MonadError (Doc ann) m => REPLState ctx n -> ExpN -> m ARes
evalTop replState expN = liftEither $ evalExpN (varNames replState) (sTyContext replState) (valContext replState) expN

evalTopCPS :: forall (n :: Nat) (m :: Type -> Type) (ctx :: [Ty]) ann b. MonadError (Doc ann) m => REPLState ctx n -> ExpN -> (forall a b. STy a -> Eval a -> Either (Doc ann) b) -> m b
evalTopCPS replState expN g = liftEither $ evalExpNCPS (varNames replState) (sTyContext replState) (valContext replState) expN g

updateStateHelper :: String -> STy ty -> Eval ty -> REPLState ctx n -> REPLState (ty : ctx) (S n)
updateStateHelper name sty res replState =
  replState
    { varNames = name :> varNames replState,
      sTyContext = sty `HCons` sTyContext replState,
      valContext = ID res `HCons` valContext replState
    }

updateState :: String -> STy ty -> Eval ty -> REPLState ctx n -> Repl ()
updateState name sty res replState = put $ AREPLState (updateStateHelper name sty res replState)

-- Completion

comp :: (Monad m, MonadState AREPLState m) => WordCompleter m
comp n = do
  AREPLState replState <- get
  return $ filter (isPrefixOf n) (toList (varNames replState))

opts :: [(String, String -> Repl ())]
opts =
  [ ("l", load . words),
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
  (ARes sty _) <- typeHelper args
  liftIO $ print (pretty sty)

compareToHaskell :: String -> String -> Repl ()
compareToHaskell hsCode varName = do
  AREPLState replState <- get
  expN@(VarN s) <- hoistErr $ runParseVar (L.pack varName)
  (ARes sTy a) <- hoistErr' $ evalTop replState expN
  maybeFasterPR <- liftIO $ replaceWithFasterPR sTy a hsCode
  case maybeFasterPR of
    Nothing -> liftIO $ print $ show $ "error in the comparison of" <+> pretty hsCode <+> "with" <+> pretty varName
    Just newPR -> updateState s sTy newPR replState
