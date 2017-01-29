{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.String
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
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
import Exp.Abs
import Exp.Layout
import Exp.ErrM
import Concrete
import qualified TypeChecker as TC
import qualified TT as C
import qualified Eval as E
import Pretty
type Interpreter a = InputT IO a

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

settings :: [String] -> Settings IO
settings ns = Settings
  { historyFile    = Nothing
  , complete       = completeWord Nothing " \t" $ return . searchFunc ns
  , autoAddHistory = True }

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags,files,[])
      | Help    `elem` flags -> putStrLn $ usageInfo usage options
      | otherwise -> case files of
       []  -> do
         putStrLn welcome
         runInputT (settings []) (loop flags [] [] TC.verboseEnv)
       [f] -> do
         putStrLn welcome
         putStrLn $ "Loading " ++ show f
         initLoop flags f
       _   -> putStrLn $ "Input error: zero or one file expected\n\n" ++
                         usageInfo usage options
    (_,_,errs) -> putStrLn $ "Input error: " ++ concat errs ++ "\n" ++
                             usageInfo usage options

-- Initialize the main loop
initLoop :: [Flag] -> FilePath -> IO ()
initLoop flags f = do
  -- Parse and type-check files
  (res,_) <- runStateT (load (dropFileName f) (dropExtension (takeFileName f))) []
  case res of
    Failed err -> do
      putStrLn $ render $ sep ["Loading failed: ",err]
      runInputT (settings []) (loop flags f [] TC.verboseEnv)
    Resolved (adefs,names) -> do
      (merr,tenv) <- TC.runDeclss TC.verboseEnv adefs
      case merr of
        Just err -> putStrLn $ render $ sep ["Type checking failed:",err]
        Nothing  -> return ()
      putStrLn "File loaded."
      -- Compute names for auto completion
      runInputT (settings [n | ((n,_),_) <- names]) (loop flags f names tenv)

-- The main loop
loop :: [Flag] -> FilePath -> [(C.Binder,SymKind)] -> TC.TEnv -> Interpreter ()
loop flags f names tenv@(TC.TEnv _ rho _ _ _) = do
  input <- getInputLine prompt
  case input of
    Nothing    -> outputStrLn help >> loop flags f names tenv
    Just ":q"  -> return ()
    Just ":r"  -> lift $ initLoop flags f
    Just (':':'l':' ':str)
      | ' ' `elem` str -> do outputStrLn "Only one file allowed after :l"
                             loop flags f names tenv
      | otherwise      -> lift $ initLoop flags str
    Just (':':'c':'d':' ':str) -> do lift (setCurrentDirectory str)
                                     loop flags f names tenv
    Just ":h"  -> outputStrLn help >> loop flags f names tenv
    Just str   -> case pExp (lexer str) of
      Bad err -> outputStrLn ("Parse error: " ++ err) >> loop flags f names tenv
      Ok  exp ->
        case runResolver [] {- FIXME -} "<interactive>" $ local (insertBinders names) $ resolveExp exp of
          Left  err  -> do outputStrLn (render ("Resolver failed:" </> err))
                           loop flags f names tenv
          Right body -> do
          x <- liftIO $ TC.runInfer tenv body
          case x of
            Left err -> do outputStrLn (render ("Could not type-check:" </> err))
                           loop flags f names tenv
            Right typ  -> do
              outputStrLn (render ("TYPE:" </> pretty typ))
              let e = E.eval rho body
              liftIO $ putStrLn (render ("EVAL:" </> pretty e))
              loop flags f names tenv

load :: String -> FilePath -> StateT Modules IO ModuleState
load prefix f = do
  (ms::Modules) <- get :: StateT Modules IO Modules
  case lookup f ms of
    Just Loading -> return $ Failed "cycle in imports"
    Just r@(Resolved _) -> return r
    Nothing -> do
      let fname = (prefix FP.</> f <.> "tt")
      b <- liftIO $ doesFileExist fname
      if not b
        then return $ Failed $ sep ["file not found: ", fromString fname]
        else do
          s <- liftIO $ readFile fname
          let ts = lexer s
          case pModule ts of
              Bad s  -> do
                return $ Failed $ sep ["Parse failed in", fromString f, fromString s]
              Ok m@(Module imp _) -> do
                forM_ imp $ \(Import i) -> load prefix (unAIdent i)
                ms' <- get
                case runResolver ms' f (resolveModule m) of
                  Left err -> return $ Failed $ sep ["Resolver error:", err]
                  Right x -> do
                    modify $ ((f,Resolved x):)
                    return (Resolved x)


help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
