{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.String
import Control.Monad.Trans.State.Strict
-- import Control.Monad.State.Class
-- import Control.Monad.Trans.RWS
-- import Control.Monad.State
import Control.Monad.Except
import Data.List
import System.Directory
import System.FilePath hiding ((</>))
import qualified System.FilePath as FP
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline

import Exp.Lex
import Exp.Par
import Exp.Print hiding (render)
import Exp.Layout
import Exp.ErrM
import Concrete
import qualified TypeChecker as TC
import qualified TT as C
import qualified Eval as E
import Pretty
type Loader = StateT InterpState IO
data InterpState = IS {mkEnv :: TC.TEnv -> TC.TEnv, names :: [String], modules :: C.Modules}
initState :: InterpState
initState = IS id [] []
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

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

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
      case pExp (lexer str) of
        Bad err -> outputStrLn ("Parse error: " ++ err)
        Ok  expr -> do
          case runResolver {- FIXME -} "<interactive>" $ resolveExp expr of
            Left  err  -> outputStrLn (render ("Resolver failed:" </> err))
            Right (body,(),_imports_ignored_here) -> do
            e <- lift get
            let (x,msgs) = TC.runInfer (mkEnv e (TC.emptyEnv (modules e))) body
            forM_ msgs $ outputStrLn . render
            case x of
              Left err -> do outputStrLn (render ("Could not type-check:" </> err))
              Right (v,typ)  -> do
                outputStrLn (render ("TYPE:" </> pretty typ))
                liftIO $ putStrLn (render ("EVAL:" </> pretty v))
      cont


load :: String -> FilePath -> Loader C.ModuleState
load prefix f = do
  liftIO $ putStrLn $ "Loading: " ++ f
  ms <- modules <$> get
  case lookup f ms of
    Just C.Loading -> return $ C.Failed "cycle in imports"
    Just r@(C.Loaded _ _) -> return r
    Just (C.Failed err) -> return (C.Failed err)
    Nothing -> do
      let fname = (prefix FP.</> f <.> "tt")
      b <- liftIO $ doesFileExist fname
      res <- if not b
        then return $ C.Failed $ sep ["file not found: ", fromString fname]
        else do
          s <- liftIO $ readFile fname
          let ts = lexer s
          case pExp ts of
              Bad err -> do
                return $ C.Failed $ sep ["Parse failed in", fromString f, fromString err]
              Ok m -> do
                case runResolver f (resolveExp m) of
                  Left err -> return $ C.Failed $ sep ["Resolver error:", err]
                  Right (t,_,imps) -> do
                    forM_ imps (load prefix)
                    ms' <- modules <$> get
                    let (x,msgs) = TC.runModule (TC.emptyEnv ms') t
                    liftIO $ forM_ msgs $ putStrLn . render
                    return x
      modify (\e -> e {modules = (f,res):modules e})
      return res

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
