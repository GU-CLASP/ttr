{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms, OverloadedStrings #-}
module TT where

import Prelude hiding (Num(..), pi)
import Data.Monoid
import Data.Dynamic
import Pretty 
import Algebra.Classes hiding (Sum)
import Data.List ((\\), nub)
type CheckedDecls = (TDecls Val,[Val],VTele)
data ModuleState
  = Loaded {moduleValue, moduleType :: Val}
  | Loading
  | Failed D

type Modules = [(String,ModuleState)]

-- | Terms

data Loc = Loc { locFile :: String
               , locPos :: (Int, Int) }
  deriving (Eq,Ord)

instance Show Loc where
  show (Loc name (i,j)) = name ++ "_L" ++ show i ++ "_C" ++ show j
instance Pretty Loc where
  pretty (Loc fname (line,col)) = pretty fname <> ":" <> pretty line <> ":" <> pretty col



type Ident  = String
type Label  = String
type Binder = (Ident,Loc)

noLoc :: String -> Binder
noLoc x = (x, Loc "" (0,0))

-- Branch of the form: c -> e
type Brc a    = (Label,Ter' a)

-- Telescope (x1 : A1) .. (xn : An)
type Tele a   = [(Binder,Rig,Ter' a)]

-- Labelled sum: c A1
type LblSum = [String]

-- Context gives type values to identifiers
type Ctxt   = [(Binder,Val)]

-- Mutual recursive definitions: (x1 : A1) .. (xn : An) and x1 = e1 .. xn = en
type Decls a  = [(Binder,Ter' a,Ter' a)]
data TDecls a = Open a {- type of the opened term -} (Ter' a) | Mutual (Decls a)
  deriving Eq

declIdents :: Decls a -> [Ident]
declIdents decl = [ x | ((x,_),_,_) <- decl]

declTers :: Decls a -> [Ter' a]
declTers decl = [ d | (_,_,d) <- decl]

declTele :: Decls a -> Tele a
declTele decl = [ (x,Free,t) | (x,t,_) <- decl]

declDefs :: Decls () -> [(Binder,Ter)]
declDefs decl = [ (x,d) | (x,_,d) <- decl]

-- Terms
type Ter = Ter' ()
type CTer = Ter' Val
data Ter' a = App (Ter' a) (Ter' a)
            | Pi String Rig (Ter' a) (Ter' a)
            | Lam Binder (Maybe (Ter' a)) (Ter' a)
            | RecordT (Tele a)
            | Record [(String,(Ter' a))]
            | Proj String (Ter' a)
            | Where (Ter' a) [TDecls a]
            | Module [TDecls a]
            | Var Ident
            | U
            -- constructor c Ms
            | Con Label
            -- branches c1 xs1  -> M1,..., cn xsn -> Mn
            | Split Loc [Brc a]
            -- labelled sum c1 A1s,..., cn Ans (assumes (ter' a)ms are constructors)
            | Sum LblSum
            | Undef Loc
            | Prim String
            | Import String a -- the value of the imported thing
            | Real Double
            | Meet (Ter' a) (Ter' a)
            | Join (Ter' a) (Ter' a)
            | Singleton (Ter' a) (Ter' a)

  deriving (Eq)

class Term a where
  freeVars :: a -> [Ident]

instance Term (TDecls a) where
  freeVars = \case
    Mutual ts -> concat [freeVars s ++ freeVars t | (_,s,t) <- ts]
    Open _ t -> freeVars t

uniqSplitFVs :: [Brc a] -> [Ident]
uniqSplitFVs = nub . concatMap (freeVars . snd)

instance Term (Ter' a) where
  freeVars = \case
     (Singleton s t) -> freeVars s ++ freeVars t
     (Import _ _) -> []
     (Real _) -> []
     (Meet s t) -> freeVars s ++ freeVars t
     (Join s t) -> freeVars s ++ freeVars t
     (Split _ ts) -> concatMap (freeVars . snd) ts
     (TT.Sum _) -> []
     (Undef _) -> []
     (Prim _) -> []
     (Module t) -> concatMap freeVars t
     (Var x) -> [x]
     U -> []
     (Con _) -> []
     (RecordT fs) -> concat [freeVars t | (_,_,t) <- fs]
     (Record fs) -> concat $ map (freeVars . snd) fs
     (Proj _ t) -> freeVars t
     (Where t u) -> freeVars t ++ concatMap freeVars u
     App s t -> freeVars s ++ freeVars t
     Pi _ _ s t  -> freeVars s ++ freeVars t
     Lam (x,_) s t -> (maybe [] freeVars s ++ freeVars t) \\ [x]


--------------------------------------------------------------------------------
-- | Values

data VTele = VEmpty | VBind Binder Rig Val (Val -> VTele)
           | VBot -- Hack!

instance Monoid VTele where
  mempty = VEmpty
  mappend VEmpty x = x
  mappend VBot _ = error "VBOT"
  mappend (VBind x r a xas) ys = VBind x r a (\v -> xas v <> ys)

teleBinders :: VTele -> [Binder]
teleBinders (VBind x _ _ f) = x:teleBinders (f $ error "teleBinders: cannot look at values")
teleBinders _ = []

data Interval a = a :.. a deriving (Eq,Show)

data BNat = Fin Integer | Inf deriving (Eq,Show)
type BNatInterval = Interval BNat
type Rig = PolarPair (BNatInterval)

data PolarPair a = PolarPair a a deriving (Eq,Show)

neutral :: a -> PolarPair a
neutral x = PolarPair x x

pattern FreeInterval :: Interval BNat
pattern FreeInterval = (Fin 0 :.. Inf)

pattern Free :: PolarPair (Interval BNat)
pattern Free = PolarPair FreeInterval FreeInterval

pattern ZeroIntvl :: Interval BNat
pattern ZeroIntvl = Fin 0 :.. Fin 0

instance AbelianAdditive BNat
instance Additive BNat where
  Inf + _ = Inf
  _ + Inf = Inf
  Fin x + Fin y = Fin (x+y)
  zero = Fin zero

instance Multiplicative BNat where
  Fin 0 * _ = Fin 0
  _ * Fin 0 = Fin 0
  Inf * _ = Inf
  _ * Inf = Inf
  Fin x * Fin y = Fin (x*y)
  one = Fin one

  -- fromInteger = Fin . fromInteger
instance Pretty BNat where
  pretty Inf = "∞"
  pretty (Fin x) = pretty x
instance (Eq a, Pretty a) => Pretty (Interval a) where
  pretty (x :.. y) | x == y = pretty x
                   | otherwise = pretty x <> ".." <> pretty y

instance Pretty Rig where
  pretty (PolarPair ZeroIntvl FreeInterval) = "-"
  pretty (PolarPair FreeInterval ZeroIntvl) = "+"
  pretty (PolarPair x y)
    | x == y = pretty x
    | otherwise = "+" <> pretty x <> " -" <> pretty y


instance Additive a => Additive (Interval a) where
  a :.. b + c :.. d = (a+c) :.. (b+d)
  zero = zero :.. zero

instance Multiplicative a => Multiplicative (Interval a) where
  a :.. b * c :.. d = (a*c) :.. (b*d)
  one = one :.. one

instance Additive a => Additive (PolarPair a) where
  a `PolarPair` b + c `PolarPair` d = (a+c) `PolarPair` (b+d)
  zero = zero `PolarPair` zero
instance (Additive a,Lattice a,Multiplicative a) => Multiplicative (PolarPair a) where
  a `PolarPair` b * c `PolarPair` d = (a*c \/ b*d) `PolarPair` (a*d \/ b*c)
  one = one `PolarPair` zero

class Lattice a where
  (/\) :: a -> a -> a
  (\/) :: a -> a -> a

instance Lattice Integer where
  (/\) = min
  (\/) = max

instance Lattice BNat where
  Inf /\ x = x
  x /\ Inf = x
  Fin x /\ Fin y = Fin (x /\ y)

  Inf \/ x = x
  x \/ Inf = x
  Fin x \/ Fin y = Fin (x \/ y)

instance Lattice a => Lattice (Interval a) where
  (a :.. b) /\ (c :.. d) = (a \/ c) :.. (b /\ d)
  (a :.. b) \/ (c :.. d) = (a /\ c) :.. (b \/ d)

instance Lattice a => Lattice (PolarPair a) where
  (a `PolarPair` b) /\ (c `PolarPair` d) = (a /\ c) `PolarPair` (b /\ d)
  (a `PolarPair` b) \/ (c `PolarPair` d) = (a \/ c) `PolarPair` (b \/ d)

instance Ord BNat where
  _ <= Inf = True
  Inf <= _ = False
  Fin x <= Fin y = x <= y
instance Ord a => Ord (Interval a) where
  a :.. b <= c :.. d = c <= a && b <= d

instance Ord a => Ord (PolarPair a) where
  PolarPair a b <= PolarPair c d = a <= c && b <= d
data Val = VU
         | Ter CTer Env
         | VPi String Rig Val Val
         | VRecordT VTele
         | VRecord [(String,Val)]
         | VSum LblSum
         | VCon Ident
         | VApp Val Val            -- the first Val must be neutral
         | VSplit Val Val          -- the second Val must be neutral
         | VVar String
         | VProj String Val
         | VLam String (Val -> Val)
         | VPrim Dynamic String
         | VAbstract String
         | VMeet Val Val
         | VJoin Val Val
         | VSingleton Val Val
  -- deriving Eq

mkVar :: Int -> Val
mkVar k = VVar ('X' : show k)

isNeutral :: Val -> Bool
isNeutral (VAbstract _) = True
isNeutral (VApp u _)   = isNeutral u
isNeutral (VSplit _ v) = isNeutral v
isNeutral (VVar _)     = True
isNeutral (VProj _ v)  = isNeutral v
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

valOfEnv :: Env -> [(Ident,Val)]
valOfEnv Empty            = []
valOfEnv (PDef _ env)     = valOfEnv env
valOfEnv (Pair env ((x,_),v)) = (x,v) : valOfEnv env
