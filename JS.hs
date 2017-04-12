{-# LANGUAGE ScopedTypeVariables #-}

module Main (
    main
) where

import Control.Monad.IO.Class (MonadIO(..))
import Control.Concurrent.MVar (takeMVar, putMVar, newEmptyMVar)
import GHCJS.DOM
import GHCJS.DOM.Types (HTMLParagraphElement(..), HTMLSpanElement(..), unsafeCastTo, HTMLTextAreaElement(..), HTMLButtonElement(..))
import GHCJS.DOM.Document (getBodyUnsafe, createElementUnsafe, createTextNode)
import GHCJS.DOM.Element (setInnerHTML)
import GHCJS.DOM.Node (appendChild)
import GHCJS.DOM.EventM (on, mouseClientXY)
import qualified GHCJS.DOM.Document as D (click)
import qualified GHCJS.DOM.Element as E (click)
import qualified GHCJS.DOM.HTMLTextAreaElement as TA (getValue)
import qualified GHCJS.DOM.HTMLButtonElement as B (getValue)
import Loader
import TT (ModuleState(..))
import Control.Monad.Trans.State.Strict
import Pretty (render, sep, text)

main = do
  putStrLn "ttr starting"
  Just doc <- currentDocument
  body <- getBodyUnsafe doc
  setInnerHTML body (Just "<h1>TTR</h1> Enter the program to check here:")

  textArea <- createElementUnsafe doc (Just "textarea") >>= unsafeCastTo HTMLTextAreaElement
  appendChild body (Just textArea)

  checkButton <- createElementUnsafe doc (Just "button") >>= unsafeCastTo HTMLButtonElement
  buttonText <- createTextNode doc "check"
  appendChild checkButton buttonText
  appendChild body (Just checkButton)

  on checkButton E.click $ do
      Just textAreaContents <- TA.getValue textArea
      newParagraph <- createElementUnsafe doc (Just "p") >>= unsafeCastTo HTMLParagraphElement
      (l,_state) <- liftIO $ runStateT (loadExpression False "" "<interactive>" textAreaContents) initState
      let (reply::String) = render $ case l of
            Failed err -> sep [text "Checking failed:",err]
            Loaded v t -> text "Checking successful."

      replyNode <- createTextNode doc reply
      appendChild newParagraph replyNode
      appendChild body (Just newParagraph)
      return ()

  exitMVar <- liftIO newEmptyMVar
  -- In case we want an exit button:
  -- exit <- createElementUnsafe doc (Just "span") >>= unsafeCastTo HTMLSpanElement
  -- text <- createTextNode doc "Click here to exit"
  -- appendChild exit text
  -- appendChild body (Just exit)
  -- on exit E.click $ liftIO $ putMVar exitMVar ()

  -- -- Force all all the lazy evaluation to be executed
  syncPoint


  -- -- In GHC compiled version the WebSocket connection will end when this
  -- -- thread ends.  So we will wait until the user clicks exit.
  liftIO $ takeMVar exitMVar
  setInnerHTML body (Just ("<h1>DONE!</h1>") )
  return ()

{-
Local Variables:
dante-target: js-ttr
dante-repl-command-line: ("nix-shell" "ghcjs.nix" "--run" "ghcjs --interactive")
End:
-}

