{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.String
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
         runInputT (settings []) (loop flags "" [] (TC.emptyEnv []))
       [f] -> do
         putStrLn welcome
         putStrLn $ "Loading " ++ show f
         initLoop flags (dropFileName f) (dropExtension (takeFileName f))
       _   -> putStrLn $ "Input error: zero or one file expected\n\n" ++
                         usageInfo usage options
    (_,_,errs) -> putStrLn $ "Input error: " ++ concat errs ++ "\n" ++
                             usageInfo usage options

-- Initialize the main loop
initLoop :: [Flag] -> FilePath -> FilePath -> IO ()
initLoop flags prefix f = do
  -- Parse and type-check files
  (res,ms) <- runStateT (load prefix f) []
  let k ns e = runInputT (settings ns) (loop flags prefix f (e (TC.emptyEnv ms)))
  case res of
    C.Failed err -> do
      putStrLn $ render $ sep ["Loading failed:",err]
      k [] id
    C.Loaded v t -> do
      putStrLn "File loaded."
      go v t k

go :: C.Val -> C.Val -> ([C.Ident] -> (TC.TEnv -> TC.TEnv) -> IO b) -> IO b
go v (C.VRecordT atele) k = k [n | (n,_) <- C.teleBinders atele]
                              (TC.addDecls (E.etaExpandRecord atele v,atele))
go v (C.VPi x _rig _a b) k = do
  putStrLn $ "Parametric module: entering with abtract parameters"
  go (E.app v (C.VVar x)) (E.app b (C.VVar x)) k
go _ t k = do putStrLn $ "Module does not have a record type, but instead:\n" ++ show t
              k [] id
      -- Compute names for auto completion

-- The main loop
loop :: [Flag] -> FilePath -> FilePath -> TC.TEnv -> Interpreter ()
loop flags prefix f tenv@(TC.TEnv _ _rho _ _ _ms) = do
  let cont = loop flags prefix f tenv
  input <- getInputLine prompt
  case input of
    Nothing    -> outputStrLn help >> cont
    Just ":q"  -> return ()
    Just ":r"  -> lift $ initLoop flags prefix f
    Just (':':'l':' ':str)
      | ' ' `elem` str -> do outputStrLn "Only one file allowed after :l"
                             cont
      | otherwise      -> lift $ initLoop flags prefix str
    Just (':':'c':'d':' ':str) -> do lift (setCurrentDirectory str)
                                     cont
    Just ":h"  -> outputStrLn help >> cont
    Just str   -> do
      case pExp (lexer str) of
        Bad err -> outputStrLn ("Parse error: " ++ err)
        Ok  expr -> do
          case runResolver {- FIXME -} "<interactive>" $ resolveExp expr of
            Left  err  -> outputStrLn (render ("Resolver failed:" </> err))
            Right (body,(),_imports_ignored_here) -> do
            let (x,msgs) = TC.runInfer tenv body
            forM_ msgs $ outputStrLn . render
            case x of
              Left err -> do outputStrLn (render ("Could not type-check:" </> err))
              Right (v,typ)  -> do
                outputStrLn (render ("TYPE:" </> pretty typ))
                liftIO $ putStrLn (render ("EVAL:" </> pretty v))
      cont


load :: String -> FilePath -> StateT C.Modules IO C.ModuleState
load prefix f = do
  liftIO $ putStrLn $ "Loading: " ++ f
  (ms::C.Modules) <- get :: StateT C.Modules IO C.Modules
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
                    ms' <- get
                    let (x,msgs) = TC.runModule (TC.emptyEnv ms') t
                    liftIO $ forM_ msgs $ putStrLn . render
                    return x
      modify ((f,res):)
      return res

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
