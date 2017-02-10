{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms, OverloadedStrings #-}
module TT where

import Data.Dynamic
import Pretty (D)
type CheckedDecls = (TDecls Val,[Val],VTele)

data ModuleState
  = Loaded {resolvedDecls :: [CheckedDecls]}
  | Loading
  | Failed D

type Modules = [(FilePath,ModuleState)]

-- | Terms

data Loc = Loc { locFile :: String
               , locPos :: (Int, Int) }
  deriving (Eq)

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j


type Ident  = String
type Label  = String
type Binder = (Ident,Loc)

noLoc :: String -> Binder
noLoc x = (x, Loc "" (0,0))

-- Branch of the form: c x1 .. xn -> e
type Brc a    = (Label,(Binder,Ter' a))

-- Telescope (x1 : A1) .. (xn : An)
type Tele a   = [(Binder,Ter' a)]

-- Labelled sum: c A1
type LblSum a = [(Binder,Ter' a)]

-- Context gives type values to identifiers
type Ctxt   = [(Binder,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
type Decls a  = [(Binder,Ter' a,Ter' a)]
data TDecls a = Open a (Ter' a) | Mutual (Decls a)
  deriving Eq

declIdents :: Decls a -> [Ident]
declIdents decl = [ x | ((x,_),_,_) <- decl]

declTers :: Decls a -> [Ter' a]
declTers decl = [ d | (_,_,d) <- decl]

declTele :: Decls a -> Tele a
declTele decl = [ (x,t) | (x,t,_) <- decl]

declDefs :: Decls () -> [(Binder,Ter)]
declDefs decl = [ (x,d) | (x,_,d) <- decl]

-- Terms
type Ter = Ter' ()
type CTer = Ter' Val
data Ter' a = App (Ter' a) (Ter' a)
            | Pi String (Ter' a) (Ter' a)
            | Lam Binder (Ter' a)
            | RecordT (Tele a)
            | Record [(String,(Ter' a))]
            | Proj String (Ter' a)
            | Where (Ter' a) [TDecls a]
            | Var Ident
            | U
            -- constructor c Ms
            | Con Label (Ter' a)
            -- branches c1 xs1  -> M1,..., cn xsn -> Mn
            | Split Loc [Brc a]
            -- labelled sum c1 A1s,..., cn Ans (assumes (ter' a)ms are constructors)
            | Sum Loc (LblSum a)
            | Undef Loc
            | Prim String
            | Real Double
            | Meet (Ter' a) (Ter' a)
            | Join (Ter' a) (Ter' a)

  deriving (Eq)

mkLams :: [String] -> Ter -> Ter
mkLams bs t = foldr Lam t [ noLoc b | b <- bs ]

--------------------------------------------------------------------------------
-- | Values

data VTele = VEmpty | VBind Binder Val (Val -> VTele)
           | VBot -- Hack!

teleBinders :: VTele -> [Binder]
teleBinders (VBind x _ f) = x:teleBinders (f $ error "teleBinders: cannot look at values")
teleBinders _ = []

data Val = VU
         | Ter CTer Env
         | VPi String Val Val
         | VRecordT VTele
         | VRecord [(String,Val)]
         | VCon Ident Val
         | VApp Val Val            -- the first Val must be neutral
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String
         | VProj String Val
         | VLam String (Val -> Val)
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
         | PDef [(Binder,CTer)] Env

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
