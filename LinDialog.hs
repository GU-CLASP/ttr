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
applyRule ruleVal ruleType state =
  let dflt = return ((ruleVal,one,zero,ruleType):state)
  in  case ruleType of
  VPi _ rRequested s t -> do
    ((v,rHave,rUsed,s'),state') <- selectEntry state
    case testErr (sub 0 [] s' s) of
      Just err -> fail (show err)
      Nothing ->
        if rRequested + rUsed <= rHave
        then applyRule (ruleVal `app` v) (t `app` v) ((v,rHave,rUsed+rRequested,s'):state')
        else dflt
  _ -> dflt


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

gatherFields :: Val -> VTele -> [(Val,Rig,Rig,Val)]
gatherFields _ VEmpty = []
gatherFields v (VBind name r t restTele) =
  ((f,r,zero,t):gatherFields v (restTele f)) where
  f = projVal (fst name) v

entrySho :: Entry -> (Rig,Rig,Val)
entrySho (_,rHave,rUsed,t) = (rHave,rUsed,t)

dialogManLoop :: State -> ModuleReader -> FilePath -> Interpreter ()
dialogManLoop state prefix f = do
  let cont = dialogManLoop state prefix f
  outputStrLn (render ("state (type):" </> pretty (map entrySho state)))
  input <- getInputLine "Linear Dialog Manager>"
  case input of
    Just ":q"  -> return ()
    Just (':':'i':' ':str) -> do
      l <- lift (loadExpression True prefix "<interactive>" str)
      case l of
        Loading -> error "Loading panic"
        Failed err -> outputStrLn (render err)
        Loaded v t -> do
          case (v,t) of
            (fields, VRecordT atele) -> do
              outputStrLn "Record found; Yes!"
              let st = gatherFields fields atele
              outputStrLn (show (length state) ++ " items found.")
              dialogManLoop st prefix f
            _ -> do
              outputStrLn "Expecting initial state as a record"
              outputStrLn ("Found instead: \n" ++ (render (pretty t)))
              cont
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
            (r, VRecordT atele) -> do
              outputStrLn "Record found; Yes!"
              let allRules = (gatherFields r atele)
              outputStrLn (show (length allRules) ++ " rules found.")
              case iterateRules 5 [(v',t') | (v',_,_,t') <- allRules] state of
                [] -> outputStrLn "The provided rule set fails after 5 iterations"
                s':_ -> dialogManLoop s' prefix f
            _ -> do
              outputStrLn "Expecting ruleset as a record"
              outputStrLn ("Found instead: \n" ++ (render (pretty t)))
              cont
    _ -> outputStrLn "Unknown command" >> cont


