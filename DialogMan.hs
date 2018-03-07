{-# LANGUAGE OverloadedStrings #-}
module DialogMan where

import Control.Monad.Except
import System.Console.Haskeline
import qualified System.FilePath as FP
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

tryApplyRule :: (Binder,Val,Val) -> (Val,Val) -> Maybe (Val,Binder,Val,Val)
tryApplyRule (binder,ruleVal,ruleType) (stateVal,stateType) =
  case ruleType of
    (VPi _nm _r a f) -> case sub 0 [stateVal] stateType a of
      Just _ -> Nothing
      Nothing -> Just (ruleType,binder,ruleVal `app` stateVal,
                       f `app` stateVal)
    _ -> Nothing


applyAnyRule :: (Val,Val) -> [(Binder,Val,Val)] -> Maybe (Val,Binder,Val,Val)
applyAnyRule st rules = foldr (<|>) Nothing [tryApplyRule r st | r <- rules]


iterateRules :: Int -> [(Binder,Val,Val)] -> (Val,Val) -> Interpreter ()
iterateRules 0 _ _ = outputStrLn "DONE!"
iterateRules n rules st = do
  case applyAnyRule st rules of
    Nothing -> outputStrLn "No rule could apply."
    Just (ruleType,binder,v,t) -> do
      outputStrLn ""
      outputStrLn (render ("Applied rule:" </> pretty binder))
      outputStrLn (render ("TYPE:" </> pretty t))
      outputStrLn (render ("EVAL:" </> pretty v))
      iterateRules (n-1) rules (v,t)

dialogMan :: Int -> ModuleReader -> FilePath -> Interpreter ()
dialogMan n prefix f = do
  -- Parse and type-check files
  res <- lift (load prefix f)
  case res of
    Failed err -> do
      outputStrLn $ render $ sep ["Loading failed:",err]
    Loaded v t -> do
      outputStrLn "File loaded."
      body n v t

body :: Int -> Val -> Val -> Interpreter ()
body n v t = case (v,t) of
   (_,VPi x _rig _a b) -> do
     outputStrLn $ "Parametric module: entering with abtract parameters"
     body n (app v (VVar x)) (app b (VVar x))

   (VRecord fields, VRecordT atele) -> do
     outputStrLn "Record found; Yes!"
     let allRules = (gatherRules fields atele) 
         initialState = (VRecord [], VRecordT VEmpty)
     outputStrLn (show (length allRules) ++ " rules found.")
     iterateRules n allRules initialState
     outputStrLn (show ())
   _ -> do
     outputStrLn "Not a record, bailing out."
     outputStrLn ("Found instead: \n" ++ (render (pretty t)))
