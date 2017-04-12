{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Loader (load, loadExpression, Loader, InterpState(..), initState) where

import Data.String
import Control.Monad.Trans.State.Strict
import Control.Monad.Except
import System.Directory
import System.FilePath hiding ((</>))
import qualified System.FilePath as FP

import Exp.Print hiding (render)
import Exp.Lex
import Exp.Par
import Exp.Layout
import Exp.ErrM
import Concrete
import qualified TypeChecker as TC
import qualified TT as C
import Pretty
type Loader = StateT InterpState IO
data InterpState = IS {mkEnv :: TC.TEnv -> TC.TEnv, names :: [String], modules :: C.Modules}
initState :: InterpState
initState = IS id [] []

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer


loadExpression :: Bool -> String -> String -> String -> StateT InterpState IO C.ModuleState
loadExpression inEnv prefix f s = do
  let ts = lexer s
  case pExp ts of
      Bad err -> do
        return $ C.Failed $ sep ["Parse failed in", fromString f, fromString err]
      Ok m -> do
        case runResolver f (resolveExp m) of
          Left err -> return $ C.Failed $ sep ["Resolver error:", err]
          Right (t,_,imps) -> do
            forM_ imps (load prefix)
            e <- get
            let (x,msgs) = TC.runModule ((if inEnv then mkEnv e else id) (TC.emptyEnv (modules e))) t
            liftIO $ forM_ msgs $ putStrLn . render
            return x

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
          loadExpression False prefix f s
      modify (\e -> e {modules = (f,res):modules e})
      return res



showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree
