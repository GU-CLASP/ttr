{-# LANGUAGE TupleSections, ParallelListComp, OverloadedStrings #-}

-- | Convert the concrete syntax into the syntax of cubical TT.
module Concrete where

import Exp.Abs
import qualified TT as C
import TT (Interval(..), Rig, free, BNat(..))
import Pretty

import Control.Monad.Trans.RWS
import Control.Monad.Trans.Except
import Control.Monad.Except (throwError)
import Control.Monad (when)
import Data.Functor.Identity
import Data.List (nub)
import Algebra.Classes hiding (Sum)

type Tele = [(AIdent,Rig,Exp)]
type Ter  = C.Ter

-- | Useful auxiliary functions

-- Applicative cons
(<:>) :: Applicative f => f a -> f [a] -> f [a]
a <:> b = (:) <$> a <*> b

-- un-something functions
unAIdent :: AIdent -> C.Ident
unAIdent (AIdent (_,x)) = x

unVar :: Exp -> Maybe AIdent
unVar (Var x) = Just x
unVar _       = Nothing

unWhere :: ExpWhere -> Exp
unWhere (Where e ds) = Let ds e
unWhere (NoWhere e)  = e

-- tail recursive form to transform a sequence of applications
-- App (App (App u v) ...) w  into (u, [v, …, w])
unApps :: Exp -> [Exp] -> (Exp, [Exp])
unApps (App u v) ws = unApps u (v : ws)
unApps u         ws = (u, ws)

-- turns an expression of the form App (... (App id1 id2) ... idn)
-- into a list of idents
pseudoIdents :: Exp -> Maybe [AIdent]
pseudoIdents = mapM unVar . uncurry (:) . flip unApps []

pseudoTele :: [PseudoTDecl] -> Maybe Tele
pseudoTele []                         = return []
pseudoTele (WPseudoTDecl expr amount typ : pd) = do
    ids <- pseudoIdents expr
    pt  <- pseudoTele pd
    return $ map (,Fin amount :.. Fin amount,typ) ids ++ pt
pseudoTele (PseudoTDecl expr typ : pd) = do
    ids <- pseudoIdents expr
    pt  <- pseudoTele pd
    return $ map (,free,typ) ids ++ pt

-------------------------------------------------------------------------------
-- | Resolver and environment

data SymKind = Variable -- TODO: delete
  deriving (Eq,Show)

-- local environment for constructors
data Env = Env { envFile :: String }

type Resolver a = RWST Env [String] () (ExceptT D Identity) a

runResolver :: FilePath -> Resolver a -> Either D (a,(),[String])
runResolver f x = runIdentity $ runExceptT $ runRWST x (Env f) ()

getModule :: Resolver String
getModule = envFile <$> ask

getLoc :: (Int,Int) -> Resolver C.Loc
getLoc l = C.Loc <$> getModule <*> pure l

resolveBinder :: AIdent -> Resolver C.Binder
resolveBinder (AIdent (l,x)) = (x,) <$> getLoc l

resolveVar :: AIdent -> Resolver Ter
resolveVar (AIdent (l,x))
  | (x == "_") || (x == "undefined") = C.Undef <$> getLoc l
  | otherwise = return $ C.Var x

lam :: AIdent -> Resolver Ter -> Resolver Ter
lam a e = do x <- resolveBinder a; C.Lam x Nothing <$> e

lams :: [AIdent] -> Resolver Ter -> Resolver Ter
lams = flip $ foldr lam

bind :: (String -> Rig -> Ter -> Ter -> Ter) -> (AIdent, Rig, Exp) -> Resolver Ter -> Resolver Ter
bind f (x@(AIdent(_,nm)),r,t) e = do
  t' <- resolveExp t
  f nm r t' <$> (C.Lam <$> resolveBinder x <*> pure (Just t') <*> e)

binds :: (String -> Rig -> Ter -> Ter -> Ter) -> Tele -> Resolver Ter -> Resolver Ter
binds f = flip $ foldr $ bind f

resolveExp :: Exp -> Resolver Ter
resolveExp (Import (AIdent (_,i))) = tell [i] >> return (C.Import i ())
resolveExp (Module dcls) = C.Module <$> resolveDecls dcls
resolveExp U            = return C.U
resolveExp (Var x)      = resolveVar x
resolveExp (App t s)    = C.App <$> resolveExp t <*> resolveExp s
resolveExp (Record t)  = case pseudoTele t of
  Just tele -> C.RecordT <$> resolveTele tele
  Nothing   -> throwError "Telescope malformed in Sigma"
resolveExp (Pi t b)     =  case pseudoTele [t] of
  Just tele -> binds C.Pi tele (resolveExp b)
  Nothing   -> throwError "Telescope malformed in Pi"
resolveExp (Fun a b)    = bind C.Pi (AIdent ((0,0),"_"), free, a) (resolveExp b)
resolveExp (LFun a b)   = bind C.Pi (AIdent ((0,0),"_"), one, a) (resolveExp b)
resolveExp (Lam x xs t) = do
  lams (x:xs) (resolveExp t)
resolveExp (TLam t u) = case pseudoTele [t] of
  Just tele -> binds (\_ _ _ -> id) tele (resolveExp u)
  Nothing -> throwError "Telescope malformed in Lambda"
resolveExp (Proj t (AIdent (_,field))) = C.Proj field <$> resolveExp t
resolveExp (Tuple fs) = C.Record <$> mapM (\(Field (AIdent (_,f)) t0) -> (f,) <$> resolveExp t0) fs
resolveExp (Split brs)  = do
    brs' <- mapM resolveBranch brs
    loc  <- getLoc (case brs of Branch (AIdent (l,_)) _ _:_ -> l ; _ -> (0,0))
    return $ C.Split loc brs'
resolveExp (Let decls e) = flip C.Where <$> resolveDecls decls <*> resolveExp e
resolveExp (Real r) = return (C.Real r)
resolveExp (PrimOp p) = return (C.Prim p)
resolveExp (And t u) = C.Meet <$> resolveExp t <*> resolveExp u
resolveExp (Or t u) = C.Join <$> resolveExp t <*> resolveExp u
resolveExp (Con (AIdent (_,n)) t) = C.Con n <$> resolveExp t
resolveExp (Singleton t u) = C.Singleton <$> resolveExp t <*> resolveExp u
resolveExp (Sum labs) = do
  labs' <- mapM resolveLabel labs
  loc <- getLoc (case labs of Label (AIdent (l,_)) _:_ -> l ; _ -> (0,0))
  return $ C.Sum loc labs'

resolveExps :: [Exp] -> Resolver [Ter]
resolveExps ts = traverse resolveExp ts

resolveWhere :: ExpWhere -> Resolver Ter
resolveWhere = resolveExp . unWhere

resolveBranch :: Branch -> Resolver (C.Label,(C.Binder,C.Ter))
resolveBranch (Branch lbl args e) = do
    binder <- resolveBinder args
    re      <- resolveWhere e
    return (unAIdent lbl, (binder, re))

resolveTele :: [(AIdent,Rig,Exp)] -> Resolver (C.Tele ())
resolveTele []        = return []
resolveTele ((i,r,d):t) = do
  x <- resolveBinder i
  ((x,r,) <$> resolveExp d) <:> (resolveTele t)

resolveLabel :: Label -> Resolver (C.Binder, C.Ter)
resolveLabel (Label n x) =
  (,) <$> resolveBinder n <*> resolveExp x

-- Resolve Data or Def declaration
resolveDDecl :: Decl -> Resolver (C.Ident, C.Ter)
resolveDDecl (DeclDef  (AIdent (_,n)) args body) =
  (n,) <$> lams args (resolveWhere body)
resolveDDecl d = throwError $ "Definition expected" <+> showy d

-- Resolve mutual declarations (possibly one)
resolveMutuals :: [Decl] -> Resolver (C.Decls ())
resolveMutuals decls = do
    let cns = names
    when (nub cns /= cns) $
      throwError $ "Duplicated constructor or ident:" <+> showy cns
    rddecls <-
      mapM (resolveDDecl) ddecls
    when (names /= map fst rddecls) $
      throwError $ "Mismatching names in" <+> showy decls
    rtdecls <- resolveTele tdecls
    return ([ (x,t,d) | (x,_r,t) <- rtdecls | (_,d) <- rddecls ])
  where
    idents = [ x | DeclType x _ <- decls ]
    names  = [ unAIdent x | x <- idents ]
    tdecls = [ (x,free,t) | DeclType x t <- decls ]
    ddecls = filter (not . isTDecl) decls
    isTDecl d = case d of DeclType{} -> True; _ -> False

-- Resolve declarations
resolveDecls :: [Decl] -> Resolver [C.TDecls ()]
resolveDecls []                   = return []
resolveDecls (DeclOpen d:ds) = do
    d' <- C.Open () <$> resolveExp d
    (rds) <- resolveDecls ds
    return (d' : rds)
resolveDecls (td@DeclType{}:d:ds) = do
    (rtd)  <- resolveMutuals [td,d]
    (rds) <- resolveDecls ds
    return (C.Mutual rtd : rds)
resolveDecls (DeclMutual defs : ds) = do
  (rdefs)  <- resolveMutuals defs
  (rds) <- resolveDecls ds
  return (C.Mutual rdefs : rds)
resolveDecls (decl:_) = throwError $ "Invalid declaration:" <+> showy decl
