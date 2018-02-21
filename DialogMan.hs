{-# LANGUAGE OverloadedStrings #-}
module DialogMan where

import Control.Monad.Trans.State.Strict
import Control.Monad.Except
import Data.List
import System.Directory
import System.FilePath hiding ((</>))
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline
import qualified System.FilePath as FP
import Data.Maybe
import Control.Applicative

import TT
import Eval
import Pretty
import Loader

type Interpreter a = InputT Loader a

gatherRules :: [(String,Val)] -> VTele -> [(Binder,Val,Val)]
gatherRules _ VEmpty = []
gatherRules ((_name',v):vs) (VBind name _ t restTele) =
  let specialVarName = "< DEPENDS >"
      restTeleTest = restTele (VVar specialVarName)
  in case specialVarName `occursIn` restTeleTest of
    True -> []
    False -> ((name,v,t):gatherRules vs restTeleTest)

tryApplyRule :: (Binder,Val,Val) -> (Val,Val) -> Maybe (Val,Val)
tryApplyRule (_,ruleVal,ruleType) (stateVal,stateType) =
  case ruleType of
    (VPi _nm _r a f) -> case sub 0 stateType a of
      Just _ -> Nothing
      Nothing -> Just (ruleVal `app` stateVal,
                       f `app` stateVal)
    _ -> Nothing


applyAnyRule :: (Val,Val) -> [(Binder,Val,Val)] -> Maybe (Val,Val)
applyAnyRule st rules = foldr (<|>) Nothing [tryApplyRule r st | r <- rules]


iterateRules :: Int -> [(Binder,Val,Val)] -> (Val,Val) -> Interpreter ()
iterateRules 0 _ _ = outputStrLn "DONE!"
iterateRules n rules st = do
  case applyAnyRule st rules of
    Nothing -> outputStrLn "No rule could apply."
    Just x@(v,t) -> do
      outputStrLn "Rule applied, result:"
      outputStrLn (render ("TYPE:" </> pretty t))
      outputStrLn (render ("EVAL:" </> pretty v))
      iterateRules (n-1) rules x

dialogMan :: ModuleReader -> FilePath -> Interpreter ()
dialogMan prefix f = do
  -- Parse and type-check files
  res <- lift (load prefix f)
  case res of
    Failed err -> do
      outputStrLn $ render $ sep ["Loading failed:",err]
    Loaded v t -> do
      outputStrLn "File loaded."
      body v t

body :: Val -> Val -> Interpreter ()
body v t = case (v,t) of
   (_,VPi x _rig _a b) -> do
     outputStrLn $ "Parametric module: entering with abtract parameters"
     body (app v (VVar x)) (app b (VVar x))

   (VRecord fields, VRecordT atele) -> do
     outputStrLn "Record found; Yes!"
     let allRules = (gatherRules fields atele) 
         initialState = (VRecord [], VRecordT VEmpty)
     outputStrLn (show (length allRules) ++ " rules found.")
     iterateRules 2 allRules initialState
     outputStrLn (show ())
   _ -> do
     outputStrLn "Not a record, bailing out."
     outputStrLn ("Found instead: \n" ++ (render (pretty t)))
