{-# LANGUAGE ScopedTypeVariables #-}

module Main (
    main
) where

import Control.Monad.IO.Class (MonadIO(..))
import Control.Concurrent.MVar (takeMVar, putMVar, newEmptyMVar)
import GHCJS.DOM
import GHCJS.DOM.Types (HTMLParagraphElement(..), HTMLSpanElement(..), unsafeCastTo, castTo, HTMLTextAreaElement(..), HTMLButtonElement(..))
import GHCJS.DOM.Document (getBodyUnsafe, createElementUnsafe, createTextNode, getElementById)
import GHCJS.DOM.Element (setInnerHTML)
import GHCJS.DOM.Node (appendChild)
import GHCJS.DOM.EventM (on, mouseClientXY)
import qualified GHCJS.DOM.Document as D (click)
import qualified GHCJS.DOM.Element as E (click)
import qualified GHCJS.DOM.HTMLTextAreaElement as TA (getValue)
import qualified GHCJS.DOM.HTMLButtonElement as B (getValue)
import qualified GHCJS.DOM.Node as N (setNodeValue)
import Loader
import TT (ModuleState(..))
import Control.Monad.Trans.State.Strict
import Pretty (render, sep, text, hang)
import JavaScript.Web.XMLHttpRequest
import qualified Data.JSString as JSS
import Data.String

demo = unlines
  ["\\(context : [Ind    : Type;",
   "             Animal : Ind -> Type;",
   "             Human  : Ind -> Type;",
   "             Dog    : Ind -> Type;",
   "             Donkey : Ind -> Type;",
   "             Hug    : Ind -> Ind -> Type;",
   "             Own    : Ind -> Ind -> Type;",
   "             a0     : Ind;",
   "             aA     : Animal a0;",
   "             aH     : Human a0;",
   "             humanIsAnimal : (x:Ind) -> Human x -> Animal x;",
   "             ]) -> module",
   "",
   "open context",
   "",
   "Anim : Type",
   "Anim = [x : Ind; isAnimal : Animal x]",
   "",
   "Huma : Type",
   "Huma = Anim /\\ [x : Ind; isHuman : Human x]",
   "",
   "a : Huma",
   "a = (x = a0, isHuman = aH, isAnimal = aA)",
   "",
   "b : Anim",
   "b = a",
   "",
   "ManOwnADonkey : Type",
   "ManOwnADonkey = [x : Ind;",
   "                 y : Ind;",
   "                 q : Animal x;",
   "                 p : Human x;",
   "                 q : Donkey y;",
   "                 o : Own x y]",
   "",
   "f : ManOwnADonkey -> Huma",
   "f r = (x = r.x, isHuman = r.p, isAnimal = r.q)",
   "",
   "ManOwnADonkey2 : Type",
   "ManOwnADonkey2 = [x : Huma;",
   "                  y : Ind;",
   "                  q : Donkey y;",
   "                  o : Own x.x y]",
   "",
   "f : ManOwnADonkey2 -> Huma",
   "f r = r.x",
   "",
   "VP : Type",
   "VP = Ind -> Type",
   "",
   "NP' : Type",
   "NP' = (verb : VP) -> [subject : Ind; holds : verb subject]",
   "",
   "S : Type",
   "S = [subject : Ind;",
   "     verb : Ind -> Type;",
   "     holds : verb subject]",
   "",
   "",
   "appVP' : VP -> NP' -> S",
   "appVP' vp np = (verb = vp, subject = s0.subject, holds = s0.holds)",
   "  where s0 : [subject : Ind; holds : vp subject]",
   "        s0 = np vp"]


main = do
  putStrLn "ttr starting"
  Just doc <- currentDocument
  body <- getBodyUnsafe doc
  setInnerHTML body (Just ("Type-theory Easter Egg<p/>  <textarea id='input' cols=80 rows=33 style='font-family: monospace;font-size:12pt'>"++ demo ++"</textarea> <p/> <button id='checkButton'>check</button> <pre id='output'></pre>"))

  Just elTextArea <- getElementById doc "input"
  Just textArea <- castTo HTMLTextAreaElement elTextArea

  Just elCheckButton <- getElementById doc "checkButton"
  Just checkButton <- castTo HTMLButtonElement elCheckButton

  Just newParagraph <- getElementById doc "output"
  Just replyNode <- createTextNode doc "<Checker output>"
  appendChild newParagraph (Just replyNode)

  on checkButton E.click $ do
      Just textAreaContents <- TA.getValue textArea
      (l,_state) <- liftIO $ runStateT (loadExpression False webModuleReader "<textarea>" textAreaContents) initState
      let (reply::String) = render $ case l of
            Failed err -> sep [text "Checking failed:",err]
            Loaded v t -> text "Checking successful."
      N.setNodeValue replyNode (Just reply)
      return ()

  -- exitMVar <- liftIO newEmptyMVar
  -- In case we want an exit button:
  -- exit <- createElementUnsafe doc (Just "span") >>= unsafeCastTo HTMLSpanElement
  -- text <- createTextNode doc "Click here to exit"
  -- appendChild exit text
  -- appendChild body (Just exit)
  -- on exit E.click $ liftIO $ putMVar exitMVar ()

  -- -- Force all all the lazy evaluation to be executed
  -- syncPoint


  -- -- In GHC compiled version the WebSocket connection will end when this
  -- -- thread ends.  So we will wait until the user clicks exit.
  -- liftIO $ takeMVar exitMVar
  -- setInnerHTML body (Just ("<h1>DONE!</h1>") )
  return ()


webModuleReader f = do
  let uri = (f ++ ".tt")
  resp <- xhrString Request
            { reqMethod          = GET
            , reqURI             = fromString uri
            , reqLogin           = Nothing
            , reqHeaders         = []
            , reqWithCredentials = False
            , reqData            = NoData
            }
  return $ case contents resp of
    Nothing -> Left $ hang 2 (text "URI could not be loaded:") (text uri)
    Just s -> Right s

{-
dante-target: js-ttr
dante-repl-command-line: ("nix-shell" "ghcjs.nix" "--run" "ghcjs --interactive")
-}

