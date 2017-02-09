{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms, FlexibleContexts, RecordWildCards, OverloadedStrings, TypeSynonymInstances, TupleSections#-}
module TypeChecker where

import Data.Function
import Data.List
import Data.Monoid hiding (Sum)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Except
import Data.String
import Pretty
import TT
import Eval

type CheckedDecls = (Decls Val,[Val],VTele)

data ModuleState
  = Loaded {resolvedDecls :: [CheckedDecls]}
  | Loading
  | Failed D

type Modules = [(FilePath,ModuleState)]


-- Type checking monad
type Typing a = ReaderT TEnv (ExceptT D IO) a

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env     :: Env
                 , ctxt    :: Ctxt
                 , errCtx  :: [D]
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }

showCtxt :: Show a => [(([Char], t), a)] -> [Char]
showCtxt ctx = intercalate ", \n" $ reverse $ [i ++ " : " ++ show v | ((i,_),v) <- ctx]

logg :: D -> Typing a -> Typing a
logg x = local (\e -> e {errCtx = x:errCtx e})

oops :: D -> Typing a
oops msg = do
  TEnv {..} <- ask
  throwError $ sep ["In: " <+> sep (map ((<> ":")) (reverse errCtx)),
                     msg,
                     "in environment" <> pretty env,
                     "in context" <+> pretty ctxt]

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 Empty [] [] True
silentEnv  = TEnv 0 Empty [] [] False

addTypeVal :: (Binder, Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k rho gam ex v) =
  TEnv (k+1) (Pair rho (x,mkVar k)) (p:gam) ex v

addTeleVal :: VTele -> TEnv -> TEnv
addTeleVal VEmpty lenv = lenv
addTeleVal (VBind x a rest) lenv = addTypeVal (x,a) (addTeleVal (rest (mkVar (index lenv))) lenv) 

-- | Add a bunch of (already checked) declarations to the environment.
addDecls :: CheckedDecls -> TEnv -> TEnv
addDecls (_,[],VEmpty) tenv = tenv
addDecls ((_:ts),(v:vs),VBind x a bs) (TEnv k rho gam ex verb) =
  addDecls (ts,vs,bs v) (TEnv k (Pair rho (x,v)) ((x,a):gam) ex verb)

trace :: String -> Typing ()
trace s = do
  b <- verbose <$> ask
  when b $ liftIO (putStrLn s)

runTyping :: TEnv -> Typing a -> IO (Either D a)
runTyping env t = runExceptT $ runReaderT t env

checkModule :: Modules -> TEnv -> [String] -> [Decls ()] -> IO (Either D [CheckedDecls])
checkModule _ tenv [] dcls = runDecls tenv dcls
checkModule ms tenv (i:is) dcls = do
  case lookup i ms of
    Nothing -> return $ Left $ sep ["unknow module:", fromString i]
    Just (Loaded dss) -> do
      checkModule ms (foldl (flip addDecls) tenv dss) is dcls

runDecls :: TEnv -> [Decls ()] -> IO (Either D [CheckedDecls])
runDecls tenv d = runTyping tenv $ checkDeclss d

runInfer :: TEnv -> Ter -> IO (Either D (CTer,Val))
runInfer lenv e = runTyping lenv (checkInfer e)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (CTer, Env)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> oops ("getLblType" <+> pretty c)
getLblType c u = oops (sep ["expected a data type for the constructor",
                              pretty c,"but got",pretty u])

getFresh :: Typing Val
getFresh = mkVar <$> index <$> ask

checkDecls :: Decls () -> Typing CheckedDecls
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  tele' <- checkTele tele
  e <- asks env
  let vtele = evalTele e tele'
  ters' <- local (addTeleVal vtele) (checks vtele ters)
  let d' = zipWith (\(b,ty) t -> (b,ty,t)) tele' ters'
  return (d',map (eval (PDef (zip (map fst tele) ters') e)) ters', vtele) -- allowing recursive definitions

checkDeclss :: [Decls ()] -> Typing [CheckedDecls]
checkDeclss [] = return []
checkDeclss (ds:dss) = do
  ds' <- checkDecls ds
  (ds':) <$> local (addDecls ds') (checkDeclss dss)

checkTele :: Tele () -> Typing (Tele Val)
checkTele []          = return []
checkTele ((x,a):xas) = do
  (aa,a') <- checkTypeEval a
  ((x,aa):) <$> local (addTypeVal (x,a')) (checkTele xas)


checkLogg :: Val -> Ter -> Typing CTer
checkLogg v t = logg (sep ["Checking that " <> pretty t, "has type " <> pretty v]) $ check v t

check :: Val -> Ter -> Typing CTer
check a t = case (a,t) of
  (_,Con c e) -> do -- FIXME: suspicious; we should expect a sum type here.
    (b,nu) <- getLblType c a
    Con c <$> check (eval nu b) e
  (VU,Sum loc bs) -> Sum loc <$> forM bs (\(l,a) -> (l,) <$> checkType a)
  (VPi _ (Ter (Sum _ cas) nu) f,Split loc ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then do Split loc <$>
                 (forM (zip ces' cas') $ \((lbl1,(bndr,term)), ((_lbl2,_),typ)) -> do
                     Lam _ term' <- check (VPi "" (eval nu typ) f) (Lam bndr term)
                     return (lbl1,(bndr,term')))
       else oops "case branches do not match the data type"
  (VPi _ a f,Lam x t)  -> do
    var <- getFresh
    Lam x <$> local (addTypeVal (x,a)) (check (app f var) t)
  (VRecordT ts, Record fs) -> do
    Record <$> checkRecord ts fs
  (VMeet w v,_) -> check w t >> check v t
  (VJoin w v,_) -> check w t `catchError` \e1 ->
                   check v t `catchError` \e2 ->
                   throwError $ sep [e1,"AND",e2]
  (_,Where e d) -> do
    d'@(dd,_,_) <- checkDecls d
    e' <- local (addDecls d') $ check a e
    return $ Where e' dd
  (_,Undef x) -> return (Undef x)
  _ -> do
    logg (sep ["Checking that" <+> pretty t, "has type" <+> pretty a]) $ do
       (t',v) <- checkInfer t
       checkSub "inferred type" a v
       return t'

-- | Check that a record has a given type
checkRecord :: VTele -> [(String,Ter)] -> Typing [(String,CTer)]
checkRecord VEmpty _ = return [] -- other fields are ignored.
checkRecord (VBind (x,l) a r) ts =
  case lookup x ts of
    Nothing -> oops $ sep ["type expects field", pretty x, "but it cannot be found in the term."]
    Just t -> do
      (tt,t') <- checkEval a t
      ((x,tt):) <$> checkRecord (r t') ts

checkEval :: Val -> Ter -> Typing (CTer,Val)
checkEval a t = do
  t' <- checkLogg a t
  (t',) <$> (eval <$> asks env <*> pure t')

checkTypeEval :: Ter -> Typing (CTer,Val)
checkTypeEval t = do
  t' <- checkType t
  e <- asks env
  return (t',eval e t')

checkSub :: D -> Val -> Val -> Typing ()
checkSub msg a v = do
    k <- index <$> ask
    case sub k v a of
      Nothing -> return ()
      Just err -> do
        oops $ sep ["In" <+> msg, pretty v <> " is not a subtype of " <> pretty a, "because " <> err]

checkType :: Ter -> Typing CTer
checkType t = do
  (t',a) <- checkInfer t
  case a of
   VU -> return t'
   _ -> oops $ sep ["expected a type, but got", pretty t, "which as type",pretty a]


-- | Infer the type of the argument
checkInfer :: Ter -> Typing (CTer,Val)
checkInfer e = case e of
  Real x -> return (Real x, real)
  Prim p -> return (Prim p,lkPrimTy p)
  Pi x' a (Lam x b) -> do
    (aa,a') <- checkTypeEval a
    b' <- local (addTypeVal (x,a')) $ checkType b
    return (Pi x' aa (Lam x b' ),VU)
  RecordT [] -> return (RecordT [], VU)
  RecordT ((x,a):as) -> do
    (aa,a') <- checkTypeEval a
    RecordT as' <- local (addTypeVal (x,a')) $ checkType (RecordT as)
    return (RecordT ((x,aa):as'), VU)
  U -> return (U,VU)                 -- U : U
  Var n -> do
    gam <- ctxt <$> ask
    case getIdent n gam of
      Just v  -> return (Var n,v)
      Nothing -> oops $ pretty n <> " is not declared"
  App t u -> do
    (t',c) <- checkInfer t
    case c of
      VPi _ a f -> do
        (u',v) <- checkEval a u
        return $ (App t' u', app f v)
      _       -> oops $ pretty c <> " is not a product"
  Proj l t -> do
    (t',a) <- checkInfer t
    e <- asks env
    case a of
      VRecordT rt -> (Proj l t',) <$> checkInferProj l (eval e t') rt
      _          -> oops $ pretty a <> " is not a record-type"
  Meet t u -> do
    t' <- checkType t
    u' <- checkType u
    return (Meet t' u', VU)
  Join t u -> do
    t' <- checkType t
    u' <- checkType u
    return (Join t' u', VU)
  Where t d -> do
    d' <- checkDecls d
    local (addDecls d') $ checkInfer t
  _ -> oops ("checkInfer " <> pretty e)

checkInferProj :: String -> {- ^ field to project-} Val -> {- ^ record value-} VTele -> {- ^ record type-} Typing Val
checkInferProj l _ VEmpty = oops $ "field not found:" <> pretty l
checkInferProj l r (VBind (x,_) a rest)
  | x == l = return a
  | otherwise = checkInferProj l r (rest (projVal x r))
checkInferProj _ _ VBot = error "checkInferProj: VBot escaped from meet"

checks :: VTele -> [Ter] -> Typing [CTer]
checks _              []     = return []
checks (VBind _ v xas) (e:es) = do
  (ee,e') <- checkEval v e
  (ee:) <$> checks (xas e') es
checks _              _      = oops "checks"
