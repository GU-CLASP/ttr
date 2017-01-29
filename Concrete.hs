{-# LANGUAGE TupleSections, ParallelListComp, OverloadedStrings #-}

-- | Convert the concrete syntax into the syntax of cubical TT.
module Concrete where

import Exp.Abs
import qualified TT as C
import Pretty

import Control.Monad.Trans.Reader
import Control.Monad.Trans.Except
import Control.Monad.Except (throwError)
import Control.Monad (when)
import Data.Functor.Identity
import Data.List (nub)

type Tele = [(AIdent,Exp)]
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
-- (cleaner than the previous version of unApps)
unApps :: Exp -> [Exp] -> (Exp, [Exp])
unApps (App u v) ws = unApps u (v : ws)
unApps u         ws = (u, ws)

vTele :: [VTDecl] -> Tele
vTele decls = [ (i, typ) | VTDecl ident ids typ <- decls, i <- ident:ids ]

-- turns an expression of the form App (... (App id1 id2) ... idn)
-- into a list of idents
pseudoIdents :: Exp -> Maybe [AIdent]
pseudoIdents = mapM unVar . uncurry (:) . flip unApps []

pseudoTele :: [PseudoTDecl] -> Maybe Tele
pseudoTele []                         = return []
pseudoTele (PseudoTDecl expr typ : pd) = do
    ids <- pseudoIdents expr
    pt  <- pseudoTele pd
    return $ map (,typ) ids ++ pt

-------------------------------------------------------------------------------
-- | Resolver and environment

data SymKind = Variable
  deriving (Eq,Show)

-- local environment for constructors
data Env = Env { envModule :: String,
                 variables :: [(C.Binder,SymKind)] }
  deriving (Eq, Show)

type Resolver a = ReaderT Env (ExceptT D Identity) a

emptyEnv :: Env
emptyEnv = Env "" []

runResolver :: Resolver a -> Either D a
runResolver x = runIdentity $ runExceptT $ runReaderT x emptyEnv

updateModule :: String -> Env -> Env
updateModule modu e = e {envModule = modu}

insertBinder :: (C.Binder,SymKind) -> Env -> Env
insertBinder (x@(n,_),var) e
  | n == "_" || n == "undefined" = e
  | otherwise                    = e {variables = (x, var) : variables e}

insertBinders :: [(C.Binder,SymKind)] -> Env -> Env
insertBinders = flip $ foldr insertBinder

insertVar :: C.Binder -> Env -> Env
insertVar x = insertBinder (x,Variable)

insertVars :: [C.Binder] -> Env -> Env
insertVars = flip $ foldr insertVar

getModule :: Resolver String
getModule = envModule <$> ask

getVariables :: Resolver [(C.Binder,SymKind)]
getVariables = variables <$> ask

getLoc :: (Int,Int) -> Resolver C.Loc
getLoc l = C.Loc <$> getModule <*> pure l

resolveBinder :: AIdent -> Resolver C.Binder
resolveBinder (AIdent (l,x)) = (x,) <$> getLoc l

resolveVar :: AIdent -> Resolver Ter
resolveVar (AIdent (l,x))
  | (x == "_") || (x == "undefined") = C.Undef <$> getLoc l
  | otherwise = do
    modName <- getModule
    vars    <- getVariables
    case C.getIdent x vars of
      Just Variable        -> return $ C.Var x
      _ -> throwError $ 
        "Cannot resolve variable" <+> pretty x <+> "at position" <+>
        pretty l <+> "in module" <+> pretty modName

lam :: AIdent -> Resolver Ter -> Resolver Ter
lam a e = do x <- resolveBinder a; C.Lam x <$> local (insertVar x) e

lams :: [AIdent] -> Resolver Ter -> Resolver Ter
lams = flip $ foldr lam

bind :: (String -> Ter -> Ter -> Ter) -> (AIdent, Exp) -> Resolver Ter -> Resolver Ter
bind f (x@(AIdent(_,nm)),t) e = f nm <$> resolveExp t <*> lam x e

binds :: (String -> Ter -> Ter -> Ter) -> Tele -> Resolver Ter -> Resolver Ter
binds f = flip $ foldr $ bind f

resolveExp :: Exp -> Resolver Ter
resolveExp U            = return C.U
resolveExp (Var x)      = resolveVar x
resolveExp (App t s)    = C.App <$> resolveExp t <*> resolveExp s
resolveExp (Record t)  = case pseudoTele t of
  Just tele -> C.RecordT <$> resolveTele tele
  Nothing   -> throwError "Telescope malformed in Sigma"
resolveExp (Pi t b)     =  case pseudoTele [t] of
  Just tele -> binds C.Pi tele (resolveExp b)
  Nothing   -> throwError "Telescope malformed in Pigma"
resolveExp (Fun a b)    = bind C.Pi (AIdent ((0,0),"_"), a) (resolveExp b)
resolveExp (Lam x xs t) = do
  lams (x:xs) (resolveExp t)
resolveExp (Proj t (AIdent (_,field))) = C.Proj field <$> resolveExp t
resolveExp (Tuple fs) = C.Record <$> mapM (\(Field (AIdent (_,f)) t0) -> (f,) <$> resolveExp t0) fs
resolveExp (Split brs)  = do
    brs' <- mapM resolveBranch brs
    loc  <- getLoc (case brs of Branch (AIdent (l,_)) _ _:_ -> l ; _ -> (0,0))
    return $ C.Split loc brs'
resolveExp (Let decls e) = do
  (rdecls,names) <- resolveDecls decls
  C.mkWheres rdecls <$> local (insertBinders names) (resolveExp e)
resolveExp (Real r) = return (C.Real r)
resolveExp (PrimOp p) = return (C.Prim p)
resolveExp (And t u) = C.Meet <$> resolveExp t <*> resolveExp u
resolveExp (Or t u) = C.Join <$> resolveExp t <*> resolveExp u
resolveExp (Con (AIdent (_,n)) t) = C.Con n <$> resolveExp t
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
    re      <- local (insertVar binder) $ resolveWhere e
    return (unAIdent lbl, (binder, re))

resolveTele :: [(AIdent,Exp)] -> Resolver C.Tele
resolveTele []        = return []
resolveTele ((i,d):t) = do
  x <- resolveBinder i
  ((x,) <$> resolveExp d) <:> local (insertVar x) (resolveTele t)

resolveLabel :: Label -> Resolver (C.Binder, C.Ter)
resolveLabel (Label n x) =
  (,) <$> resolveBinder n <*> resolveExp x

-- Resolve Data or Def declaration
resolveDDecl :: Decl -> Resolver (C.Ident, C.Ter)
resolveDDecl (DeclDef  (AIdent (_,n)) args body) =
  (n,) <$> lams args (resolveWhere body)
resolveDDecl d = throwError $ "Definition expected" <+> showy d

-- Resolve mutual declarations (possibly one)
resolveMutuals :: [Decl] -> Resolver (C.Decls,[(C.Binder,SymKind)])
resolveMutuals decls = do
    binders <- mapM resolveBinder idents
    let cns = names
    when (nub cns /= cns) $
      throwError $ "Duplicated constructor or ident:" <+> showy cns
    rddecls <-
      mapM (local (insertVars binders) . resolveDDecl) ddecls
    when (names /= map fst rddecls) $
      throwError $ "Mismatching names in" <+> showy decls
    rtdecls <- resolveTele tdecls
    return ([ (x,t,d) | (x,t) <- rtdecls | (_,d) <- rddecls ],
            map (,Variable) binders)
  where
    idents = [ x | DeclType x _ <- decls ]
    names  = [ unAIdent x | x <- idents ]
    tdecls = [ (x,t) | DeclType x t <- decls ]
    ddecls = filter (not . isTDecl) decls
    isTDecl d = case d of DeclType{} -> True; _ -> False

-- Resolve declarations
resolveDecls :: [Decl] -> Resolver ([C.Decls],[(C.Binder,SymKind)])
resolveDecls []                   = return ([],[])
resolveDecls (td@DeclType{}:d:ds) = do
    (rtd,names)  <- resolveMutuals [td,d]
    (rds,names') <- local (insertBinders names) $ resolveDecls ds
    return (rtd : rds, names' ++ names)
resolveDecls (DeclMutual defs : ds) = do
  (rdefs,names)  <- resolveMutuals defs
  (rds,  names') <- local (insertBinders names) $ resolveDecls ds
  return (rdefs : rds, names' ++ names)
resolveDecls (decl:_) = throwError $ "Invalid declaration:" <+> showy decl

resolveModule :: Module -> Resolver ([C.Decls],[(C.Binder,SymKind)])
resolveModule (Module n _imports decls) =
  local (updateModule $ unAIdent n) $ resolveDecls decls

resolveModules :: [Module] -> Resolver ([C.Decls],[(C.Binder,SymKind)])
resolveModules []         = return ([],[])
resolveModules (modu:mods) = do
  (rmod, names)  <- resolveModule modu
  (rmods,names') <- local (insertBinders names) $ resolveModules mods
  return (rmod ++ rmods, names' ++ names)
