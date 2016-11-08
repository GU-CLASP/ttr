{-# LANGUAGE PatternSynonyms #-}
module TT where

import Pretty
--------------------------------------------------------------------------------
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
         | Sigma Ter Ter
         | SPair Ter Ter
         | Fst Ter
         | Snd Ter
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

data Val = VU
         | Ter Ter Env
         | VPi Val Val
         | VSigma Val Val
         | VSPair Val Val
         | VCon Ident [Val]
         | VApp Val Val            -- the first Val must be neutral
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String
         | VFst Val
         | VSnd Val

         | VLam (Val -> Val)
  -- deriving Eq

mkVar :: Int -> Val
mkVar k = VVar ('X' : show k)

isNeutral :: Val -> Bool
isNeutral (VApp u _)   = isNeutral u
isNeutral (VSplit _ v) = isNeutral v
isNeutral (VVar _)     = True
isNeutral (VFst v)     = isNeutral v
isNeutral (VSnd v)     = isNeutral v
isNeutral _            = False

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Pair Env (Binder,Val)
         | PDef [(Binder,Ter)] Env
  -- deriving Eq
  
instance Show Env where
  show e0 = case e0 of
    Empty            -> ""
    (PDef _xas env)   -> show env
    (Pair env ((x,_),u)) -> show env ++ ", " ++ show (x,u)

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

instance Show Ter where
  show = showTer

showTer :: Ter -> String
showTer U             = "U"
showTer (App e0 e1)   = showTer e0 <+> showTer1 e1
showTer (Pi e0 e1)    = "Pi" <+> showTers [e0,e1]
showTer (Lam (x,_) e) = '\\' : x <+> "->" <+> showTer e
showTer (Fst e)       = showTer e ++ ".1"
showTer (Snd e)       = showTer e ++ ".2"
showTer (Sigma e0 e1) = "Sigma" <+> showTers [e0,e1]
showTer (SPair e0 e1) = "pair" <+> showTers [e0,e1]
showTer (Where e d)   = showTer e <+> "where" <+> showDecls d
showTer (Var x)       = x
showTer (Con c es)    = c <+> showTers es
showTer (Split l _)   = "split " ++ show l
showTer (Sum l _)     = "sum " ++ show l
showTer (Undef _)     = "undefined (1)"

showTers :: [Ter] -> String
showTers = hcat . map showTer1

showTer1 :: Ter -> String
showTer1 U           = "U"
showTer1 (Con c [])  = c
showTer1 (Var x)     = x
showTer1 u@(Split{}) = showTer u
showTer1 u@(Sum{})   = showTer u
showTer1 u           = parens $ showTer u

showDecls :: Decls -> String
showDecls defs = ccat (map (\((x,_),_,d) -> x <+> "=" <+> show d) defs)

namesFrom :: [Char] -> [[Char]]
namesFrom xs = [x ++ n | n <- "":map show [(1::Int)..], x <- map (:[]) xs]

instance Show Val where
  show = showVal $ namesFrom ['α'..'ω']

showVal :: [String] -> Val -> String
showVal [] _ = error "showVal: out of names"
showVal su@(s:ss) t0 = case t0 of
  VU            -> "U"
  (Ter t env)  -> show t <+> show env
  (VCon c us)  -> c <+> showVals su us
  (VPi a f)    -> "Pi" <+> svs [a,f]
  (VApp u v)   -> sv u <+> sv1 v
  (VSplit u v) -> sv u <+> sv1 v
  (VVar x)     -> x
  (VSPair u v) -> "pair" <+> svs [u,v]
  (VSigma u v) -> "Sigma" <+> svs [u,v]
  (VFst u)     -> sv u ++ ".1"
  (VSnd u)     -> sv u ++ ".2"
  (VLam f)  -> "\\" ++ s ++ " -> " <+> showVal ss (f $ VVar s)
 where sv = showVal su
       sv1 = showVal1 su
       svs = showVals su

showVals :: [String] -> [Val] -> String
showVals su = hcat . map (showVal1 su)

showVal1 :: [String] -> Val -> String
showVal1 _ VU          = "U"
showVal1 _ (VCon c []) = c
showVal1 su u@(VVar{})  = showVal su u
showVal1 su u           = parens $ showVal su u
