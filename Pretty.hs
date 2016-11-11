{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- Common functions used for pretty printing.
module Pretty where
import Control.Monad.State
import Data.String
import Data.Monoid
--------------------------------------------------------------------------------
-- | Pretty printing combinators. Use the same names as in the pretty library.

type Sho a = State [String] a
type D = Sho String

getSupply :: Sho String
getSupply = do
  (x:xs) <- get
  put xs
  return x

(<+>) :: D -> D -> D
x  <+> y  = do
 x' <- x
 y' <- y
 return (x' ++ " " ++ y')

infixr 6 <+>

hcat :: [D] -> D
hcat []     = return []
hcat [x]    = x
hcat (x:xs) = x <+> hcat xs

ccat :: [D] -> D
ccat []     = return []
ccat [x]    = x
ccat (x:xs) = x <+> return "," <+> ccat xs

parens :: D -> D
parens  = ((\p -> "(" ++ p ++ ")") <$>)

instance Monoid D where
  mempty = return ""
  mappend = liftM2 (++)

instance IsString D where
  fromString = return

namesFrom :: [Char] -> [[Char]]
namesFrom xs = [x ++ n | n <- "":map show [(1::Int)..], x <- map (:[]) xs]

runD :: D -> String
runD d = fst $ runState d (namesFrom ['α'..'ω'])

($$) :: D -> D -> D
d $$ e = d <> return "\n" <> e -- FIXME

class Pretty a where
  pretty :: a -> D

instance Pretty String where
  pretty = return

instance (Pretty a, Pretty b) => Pretty (a,b) where
  pretty (x,y) = "(" <> pretty x <> "," <> pretty y <> ")"

showy :: Show a => a -> D
showy = return . show

