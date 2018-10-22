{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

module LinDialog where

import Control.Arrow (second)
import Prelude hiding (Num(..), pi)
import Pretty
import TT
import Algebra.Classes hiding (Sum)
import Control.Monad.Except

import System.Console.Haskeline

import Eval
import Loader

type Interpreter a = InputT Loader a

type Entry = (Val,Rig,Rig,Val) -- ^ value, have, used already, type
type State = [Entry]

type Rule = (Val,Val)

selectEntry :: State -> [(Entry,State)]
selectEntry [] = []
selectEntry (x:xs) = (x,xs):map (second (x:)) (selectEntry xs)


applyRule :: Val -> Val -> State -> [State]
applyRule ruleVal ruleType state = case ruleType of
  VPi _ r s t -> do
    ((v,rHave,rUsed,s'),state') <- selectEntry state
    case testErr (sub 0 [] s' s) of
      Just err -> fail (show err)
      Nothing -> do
        guard (r + rUsed <= rHave)
        applyRule (ruleVal `app` v) (t `app` v) ((v,rHave,rUsed+r,s'):state')
  _ -> return ((ruleVal,one,zero,ruleType):state)


applyAnyRule :: [Rule] -> State -> [State]
applyAnyRule rules state = do
  (v,t) <- rules
  applyRule v t state

iterateRules :: Int -> [Rule] -> State -> [State]
iterateRules 0 _rules st = do
  return st
iterateRules n rules st = do
  s' <- applyAnyRule rules st
  iterateRules (n-1) rules s'


dialogMan :: ModuleReader -> FilePath -> Interpreter ()
dialogMan = dialogManLoop []

gatherRules :: [(String,Val)] -> VTele -> [(Val,Val)]
gatherRules _ VEmpty = []
gatherRules ((_name',v):vs) (VBind name _ t restTele) =
  let specialVarName = "< DEPENDS >"
      restTeleTest = restTele (VVar specialVarName)
  in case specialVarName `occursIn` restTeleTest of
    True -> []
    False -> ((v,t):gatherRules vs restTeleTest)

dialogManLoop :: State -> ModuleReader -> FilePath -> Interpreter ()
dialogManLoop state prefix f = do
  let cont = dialogManLoop state prefix f
  outputStrLn (render ("state value:" </> pretty state))
  input <- getInputLine "Linear Dialog Manager>"
  case input of
    Just ":q"  -> return ()
    Just (':':'a':' ':str) -> do
      l <- lift (loadExpression True prefix "<interactive>" str)
      case l of
        Loading -> error "Loading panic"
        Failed err -> outputStrLn (render err)
        Loaded v t -> do
          case applyRule v t state of
            [] -> do
              outputStrLn "The provided rule does not apply!"
              cont
            s':_ -> do
              outputStrLn "Rule applied"
              dialogManLoop s' prefix f
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
              case iterateRules 5 allRules state of
                [] -> outputStrLn "The provided rule set fails after 5 iterations"
                s':_ -> dialogManLoop s' prefix f
            _ -> do
              outputStrLn "Expecting ruleset as a record"
              outputStrLn ("Found instead: \n" ++ (render (pretty t)))
              cont
    _ -> outputStrLn "Unknown command" >> cont


