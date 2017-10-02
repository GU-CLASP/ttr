{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- Common functions used for pretty printing.
module Pretty where
import Text.PrettyPrint.Compact as PC
import Control.Monad.Reader
import Data.String
import Data.Char (isDigit)
import qualified Data.Map as M

--------------------------------------------------------------------------------
-- | Pretty printing combinators. Use the same names as in the pretty library.

type Sho a = Reader (M.Map String Int) a
type D = Sho (Doc ())


withVar :: String -> (String -> Sho a) -> Sho a
withVar s k = do
  nextIdx <- ask
  let (reverse -> idx,reverse -> name) = span isDigit (reverse s)
      i = max (if null idx then Nothing else Just (read idx)) (M.lookup name nextIdx)
  local (M.insert name (maybe 0 (+1) i)) (k (name ++ maybe "" show i))

(<+>) :: D -> D -> D
(<+>)  = liftM2 (PC.<+>)

($$) :: D -> D -> D
($$)  = liftM2 (PC.$$)

(</>) :: D -> D -> D
x </> y  = Pretty.sep [x,y]

infixr 6 <+>

instance IsString D where
  fromString = Pretty.text

text = return . PC.text

namesFrom :: [Char] -> [[Char]]
namesFrom xs = [x ++ n | n <- "":map show [(1::Int)..], x <- map (:[]) xs]

render :: D -> String
render d = PC.render $ runReader d M.empty

instance Show D where
  show = Pretty.render

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

instance Pretty Integer where
  pretty = showy

instance {-# OVERLAPPABLE #-} Pretty a => Pretty [a] where
  pretty = Pretty.list . map pretty

instance {-# OVERLAPS #-} Pretty String where
  pretty = fromString


instance (Pretty a, Pretty b) => Pretty (a,b) where
  pretty (x,y) = "(" <> pretty x <> "," <> pretty y <> ")"

