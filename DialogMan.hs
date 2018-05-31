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

tryApplyRule :: (a,Val,Val) -> (Val,Val) -> Maybe (a,Val,Val)
tryApplyRule (binder,ruleVal,ruleType) (stateVal,stateType) =
  case ruleType of
    (VPi _nm _r a f) -> case sub 0 [stateVal] stateType a of
      Err _ -> Nothing
      NoErr -> Just (binder,ruleVal `app` stateVal,
                       f `app` stateVal)
    _ -> Nothing


applyAnyRule :: (Val,Val) -> [(a,Val,Val)] -> Maybe (a,Val,Val)
applyAnyRule st rules = foldr (<|>) Nothing [tryApplyRule r st | r <- rules]


iterateRules :: Int -> [(Binder,Val,Val)] -> (Val,Val) -> Interpreter (Val,Val)
iterateRules 0 _ st = do
  outputStrLn "DONE!"
  return st
iterateRules n rules st = do
  case applyAnyRule st rules of
    Nothing -> do
      outputStrLn "No rule could apply."
      return st
    Just (binder,v,t) -> do
      outputStrLn ""
      outputStrLn (render ("Applied rule:" </> pretty binder))
      outputStrLn (render ("TYPE:" </> pretty t))
      outputStrLn (render ("EVAL:" </> pretty v))
      iterateRules (n-1) rules (v,t)

dialogMan :: ModuleReader -> FilePath -> Interpreter ()
dialogMan = dialogManLoop (VRecord []) (VRecordT VEmpty)

dialogManLoop :: Val -> Val -> ModuleReader -> FilePath -> Interpreter ()
dialogManLoop state stateTyp prefix f = do
  let cont = dialogManLoop state stateTyp prefix f
  outputStrLn (render ("state type:" </> pretty stateTyp))
  outputStrLn (render ("state value:" </> pretty state))
  input <- getInputLine "Dialog man>"
  case input of
    Just ":q"  -> return ()
    Just (':':'a':' ':str) -> do
      l <- lift (loadExpression True prefix "<interactive>" str)
      case l of
        Loading -> error "Loading panic"
        Failed err -> outputStrLn (render err)
        Loaded v t -> do
          case tryApplyRule ("interactive" :: String,v,t) (state,stateTyp) of
            Nothing -> do
              outputStrLn "The provided rule does not apply!"
              cont
            Just (_,v',t') -> do
              outputStrLn "Rule applied"
              dialogManLoop v' t' prefix f
    Just (':':'s':' ':str) -> do
      l <- lift (loadExpression True prefix "<interactive>" str)
      case l of
        Loading -> error "Loading panic"
        Failed err -> outputStrLn (render err)
        Loaded v t -> do
          case (v,t) of
            (VRecord fields, VRecordT atele) -> do
              outputStrLn "Record found; Yes!"
              let allRules = (gatherRules fields atele) 
              outputStrLn (show (length allRules) ++ " rules found.")
              (v',t') <- iterateRules 1 allRules (state,stateTyp)
              dialogManLoop v' t' prefix f
            _ -> do
              outputStrLn "Expecting ruleset as a record"
              outputStrLn ("Found instead: \n" ++ (render (pretty t)))
              cont
    _ -> outputStrLn "Unknown command" >> cont


