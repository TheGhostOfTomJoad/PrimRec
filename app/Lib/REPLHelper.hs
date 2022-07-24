module Lib.REPLHelper (hoistErr, help, defaultMatcher, ini, final, hoistErr') where

import Control.Monad.Catch
import Control.Monad.Except
import System.Console.Repline
  ( CompletionFunc,
    ExitDecision (Exit),
    HaskelineT,
    abort,
    fileCompleter,
  )

hoistErr :: (MonadIO m, Show a1, MonadThrow m) => Either a1 a2 -> HaskelineT m a2
hoistErr (Right val) = return val
hoistErr (Left err) = do
  liftIO $ print err
  abort

hoistErr' :: (MonadIO m, Show a1, MonadThrow m) => Except a1 a2 -> HaskelineT m a2
hoistErr' x = hoistErr $ runExcept x

-- Commands
help :: (MonadIO m, Show a) => a -> m ()
help args = liftIO $ print $ "Help!" ++ show args

ini :: MonadIO m => m ()
ini = liftIO $ putStrLn "\n\nHello!\n\n"

final :: MonadIO m => m ExitDecision
final = do
  liftIO $ putStrLn "Goodbye!"
  return Exit

defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher =
  [ (":l", fileCompleter)
  ]
