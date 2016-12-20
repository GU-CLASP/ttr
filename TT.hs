{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms, OverloadedStrings #-}
module TT where

import Data.Monoid hiding (Sum)
import Pretty
import Data.Dynamic

-- | Terms

data Loc = Loc { locFile :: String
               , locPos :: (Int, Int) }
  deriving Eq

type Ident  = String
type Label  = String
type Binder = (Ident,Loc)

noLoc :: String -> Binder
noLoc x = (x, Loc "" (0,0))

-- Branch of the form: c x1 .. xn -> e
type Brc    = (Label,([Binder],Ter))

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Binder,Ter)]

-- Labelled sum: c (x1 : A1) .. (xn : An)
type LblSum = [(Binder,Tele)]

-- Context gives type values to identifiers
type Ctxt   = [(Binder,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
type Decls  = [(Binder,Ter,Ter)]

declIdents :: Decls -> [Ident]
declIdents decl = [ x | ((x,_),_,_) <- decl]

declTers :: Decls -> [Ter]
declTers decl = [ d | (_,_,d) <- decl]

declTele :: Decls -> Tele
declTele decl = [ (x,t) | (x,t,_) <- decl]

declDefs :: Decls -> [(Binder,Ter)]
declDefs decl = [ (x,d) | (x,_,d) <- decl]

-- Terms
data Ter = App Ter Ter
         | Pi Ter Ter
         | Lam Binder Ter
         | RecordT Tele
         | Record [(String,Ter)]
         | Proj String Ter
         | Where Ter Decls
         | Var Ident
         | U
         -- constructor c Ms
         | Con Label [Ter]
         -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Loc [Brc]
         -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Binder LblSum
         | Undef Loc
         | Prim String
         | Real Double
         | Meet Ter Ter
         | Join Ter Ter

  deriving Eq

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkLams :: [String] -> Ter -> Ter
mkLams bs t = foldr Lam t [ noLoc b | b <- bs ]

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Values

data VTele = VEmpty | VBind Ident Val (Val -> VTele)
           | VBot -- Hack!

data Val = VU
         | Ter Ter Env
         | VPi Val Val
         | VRecordT VTele
         | VRecord [(String,Val)]
         | VCon Ident [Val]
         | VApp Val Val            -- the first Val must be neutral
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String
         | VProj String Val
         | VLam (Val -> Val)
         | VPrim Dynamic String
         | VAbstract String
         | VMeet Val Val
         | VJoin Val Val
  -- deriving Eq

mkVar :: Int -> Val
mkVar k = VVar ('X' : show k)

isNeutral :: Val -> Bool
isNeutral (VAbstract _) = True
isNeutral (VApp u _)   = isNeutral u
isNeutral (VSplit _ v) = isNeutral v
isNeutral (VVar _)     = True
isNeutral (VProj _ v)     = isNeutral v
isNeutral _            = False

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Pair Env (Binder,Val)
         | PDef [(Binder,Ter)] Env

upds :: Env -> [(Binder,Val)] -> Env
upds = foldl Pair

lookupIdent :: Ident -> [(Binder,a)] -> Maybe (Binder, a)
lookupIdent x defs = lookup x [ (y,((y,l),t)) | ((y,l),t) <- defs]

getIdent :: Ident -> [(Binder,a)] -> Maybe a
getIdent x defs = snd <$> lookupIdent x defs

valOfEnv :: Env -> [Val]
valOfEnv Empty            = []
valOfEnv (PDef _ env)     = valOfEnv env
valOfEnv (Pair env (_,v)) = v : valOfEnv env

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j

instance Pretty Ter where
  pretty = showTer

showTele :: Tele -> D
showTele [] = mempty
showTele (((x,_loc),t):tele) = (pretty x <> " : " <> showTer t <> ";") $$ showTele tele

showTer :: Ter -> D
showTer U             = "U"
showTer (Meet e0 e1)  = showTer e0 <+> "/\\" <+> showTer e1
showTer (Join e0 e1)  = showTer e0 <+> "\\/" <+> showTer e1
showTer (App e0 e1)   = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)    = "Pi" <+> showTers [e0,e1]
showTer (Lam (x,_) e) = "\\" <> pretty x <+> "->" <+> showTer e
showTer (Proj l e)       = showTer e <> "." <> pretty l
showTer (RecordT ts)  = "[" <> showTele ts <> "]"
showTer (Record fs)   = "(" <> hcat [pretty l <> " = " <> showTer e | (l,e) <- fs] <> ")"
showTer (Where e d)   = showTer e <+> "where" <+> showDecls d
showTer (Var x)       = pretty x
showTer (Con c es)    = pretty c <+> showTers es
showTer (Split l _)   = "split " <> pretty l
showTer (Sum l _)     = "sum " <> pretty l
showTer (Undef _)     = "undefined (1)"
showTer (Real r)      = showy r
showTer (Prim n)      = showy n

instance Pretty Loc where
  pretty (Loc x l) = pretty x <> "@" <> pretty l

showTers :: [Ter] -> D
showTers = hcat . map showTer1

showTer1 :: Ter -> D
showTer1 U           = "U"
showTer1 (Con c [])  = pretty c
showTer1 (Var x)     = pretty x
showTer1 u@(Split{}) = showTer u
showTer1 u@(Sum{})   = showTer u
showTer1 u           = parens $ showTer u

showDecls :: Decls -> D
showDecls defs = vcat (map (\((x,_),_,d) -> pretty x <+> "=" <+> pretty d) defs)


instance Show Ter where
  show = render . pretty

