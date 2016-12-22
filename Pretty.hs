{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- Common functions used for pretty printing.
module Pretty where
import Text.PrettyPrint.Compact as PC
import Control.Monad.State
import Data.String
import Data.Traversable
--------------------------------------------------------------------------------
-- | Pretty printing combinators. Use the same names as in the pretty library.

type Sho a = State [String] a
type D = Sho Doc

getSupply :: Sho String
getSupply = do
  (x:xs) <- get
  put xs
  return x

(<+>) :: D -> D -> D
(<+>)  = liftM2 (PC.<+>)

(<|>) :: D -> D -> D
(<|>)  = liftM2 (PC.<|>)

($$) :: D -> D -> D
($$)  = liftM2 (PC.$$)

x </> y  = Pretty.sep [x,y]

infixr 6 <+>

instance IsString D where
  fromString = return . text

namesFrom :: [Char] -> [[Char]]
namesFrom xs = [x ++ n | n <- "":map show [(1::Int)..], x <- map (:[]) xs]

render :: D -> String
render d = PC.render $ fst $ runState d (namesFrom ['α'..'ω'])

class Pretty a where
  pretty :: a -> D

instance Monoid D where
  mappend = liftM2 (<>)
  mempty = return mempty

showy :: Show a => a -> D
showy = fromString . show

parens :: D -> D
parens = liftM PC.parens
brackets :: D -> D
brackets = liftM PC.brackets

hcat :: [D] -> D
hcat xs = PC.hcat <$> (sequence xs)

vcat :: [D] -> D
vcat xs = PC.vcat <$> (sequence xs)

list :: [D] -> D
list xs = PC.list <$> (sequence xs)

-- tupled :: [D] -> D
-- tupled xs = PC.tupled <$> (sequence xs)

tupled :: [D] -> D
tupled xs = PC.tupled <$> (sequence xs)

encloseSep :: D -> D -> D -> [D] -> D
encloseSep left right sp ds = PC.encloseSep <$> left <*> right <*> sp <*> sequence ds

hang :: Int -> D -> D -> D
hang n x y = PC.hang n <$> x <*> y


hsep :: [D] -> D
hsep xs = PC.hsep <$> (sequence xs)

sep :: [D] -> D
sep xs = PC.sep <$> (sequence xs)

instance Pretty Int where
  pretty = showy

instance {-# OVERLAPPABLE #-} Pretty a => Pretty [a] where
  pretty = Pretty.list . map pretty

instance {-# OVERLAPS #-} Pretty String where
  pretty = fromString


instance (Pretty a, Pretty b) => Pretty (a,b) where
  pretty (x,y) = "(" <> pretty x <> "," <> pretty y <> ")"

