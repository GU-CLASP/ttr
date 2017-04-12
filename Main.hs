{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Trans.State.Strict
import Control.Monad.Except
import Data.List
import System.Directory
import System.FilePath hiding ((</>))
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline

import qualified TypeChecker as TC
import qualified TT as C
import qualified Eval as E
import Pretty
import Loader

type Interpreter a = InputT Loader a

-- Flag handling
data Flag = Debug | Help | Version
  deriving (Eq,Show)

options :: [OptDescr Flag]
options = [ Option "d" ["debug"]   (NoArg Debug)   "run in debugging mode"
          , Option ""  ["help"]    (NoArg Help)    "print help" ]

-- Version number, welcome message, usage and prompt strings
welcome, usage, prompt :: String
welcome = "ttr\n"
usage   = "Usage: ttr [options] <file.tt>\nOptions:"
prompt  = "> "

-- Used for auto completion
searchFunc :: [String] -> String -> [Completion]
searchFunc ns str = map simpleCompletion $ filter (str `isPrefixOf`) ns

settings :: Settings Loader
settings = Settings
  { historyFile    = Nothing
  , complete       = completeWord Nothing " \t" $ \str -> do
      ns <- names <$> get
      return (searchFunc ns str)
  , autoAddHistory = True }

main :: IO ()
main = do
  args <- getArgs
  putStrLn welcome
  case getOpt Permute options args of
    (flags,files,[])
      | Help    `elem` flags -> putStrLn $ usageInfo usage options
      | otherwise -> case files of
       []  -> do
         return ()
       [f] -> do
         putStrLn $ "Loading " ++ show f
         let p = initLoop flags (dropFileName f) (dropExtension (takeFileName f))
         _ <- runStateT (runInputT settings p) initState
         return ()
       _   -> putStrLn $ "Input error: zero or one file expected\n\n" ++
                         usageInfo usage options
    (_,_,errs) -> putStrLn $ "Input error: " ++ concat errs ++ "\n" ++
                             usageInfo usage options

-- Initialize the main loop
initLoop :: [Flag] -> FilePath -> FilePath -> Interpreter ()
initLoop flags prefix f = do
  -- Parse and type-check files
  res <- lift (load prefix f)
  case res of
    C.Failed err -> do
      outputStrLn $ render $ sep ["Loading failed:",err]
    C.Loaded v t -> do
      outputStrLn "File loaded."
      go v t
  loop flags prefix f

-- setTcEnv :: MonadState InterpState m => [String] -> (TC.TEnv -> TC.TEnv) -> m ()
setTcEnv ns mk = modify (\st -> st {mkEnv = mk, names = ns})

go :: C.Val -> C.Val -> Interpreter ()
go v (C.VRecordT atele) = lift $ setTcEnv [n | (n,_) <- C.teleBinders atele]
                                          (TC.addDecls (E.etaExpandRecord atele v,atele))
go v (C.VPi x _rig _a b) = do
  outputStrLn $ "Parametric module: entering with abtract parameters"
  go (E.app v (C.VVar x)) (E.app b (C.VVar x))
go _ t = outputStrLn $ "Module does not have a record type, but instead:\n" ++ show t


-- The main loop
loop :: [Flag] -> FilePath -> FilePath -> Interpreter ()
loop flags prefix f = do
  let cont = loop flags prefix f
  input <- getInputLine prompt
  case input of
    Nothing    -> outputStrLn help >> cont
    Just ":q"  -> return ()
    Just ":r"  -> initLoop flags prefix f
    Just (':':'l':' ':str)
      | ' ' `elem` str -> do outputStrLn "Only one file allowed after :l"
                             cont
      | otherwise      -> initLoop flags prefix str
    Just (':':'c':'d':' ':str) -> do liftIO (setCurrentDirectory str)
                                     cont
    Just ":h"  -> outputStrLn help >> cont
    Just str   -> do
      l <- lift (loadExpression True prefix "<interactive>" str)
      case l of
        C.Failed err -> outputStrLn (render err)
        C.Loaded v typ -> do
          outputStrLn (render ("TYPE:" </> pretty typ))
          liftIO $ putStrLn (render ("EVAL:" </> pretty v))
      cont


help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
