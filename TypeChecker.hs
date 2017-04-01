{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternSynonyms, FlexibleContexts, RecordWildCards, OverloadedStrings, TypeSynonymInstances, TupleSections#-}
module TypeChecker where

import Prelude hiding (pi, Num(..))
import Data.Function
import Data.Either (either)
import Data.List
import Data.Monoid hiding (Sum)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Writer hiding (Sum)
import Control.Monad.Reader
import Control.Monad.State
import Data.String
import Pretty
import TT
import Eval
import qualified Data.Map.Strict as M

import Algebra.Classes hiding (Sum(..))

type Recordoid = ([Val],VTele)
type Usages = M.Map Binder Rig

-- | Type checking monad
newtype Typing a = Typing (
  (StateT Usages)
  ((ReaderT TEnv)
  ((ExceptT D)
  (Writer [D]))) a)
 deriving (Functor, Applicative, Monad, MonadReader TEnv, MonadError D, MonadWriter [D], MonadState Usages)

-- | Scale the argument usages
relax :: Rig -> Typing a -> Typing a
relax f t = do
  r0 <- get
  put zero
  x <- t
  r1 <- get
  put (r0 + fmap (f *) r1)
  return x

use :: Binder -> Typing ()
use x = modify (+ M.singleton x one)

checkUsage :: Binder -> Rig -> Typing a -> Typing a
checkUsage b@(name,loc) br k = do
  modify (M.insert b zero)
  x <- k
  r0 <- get
  case M.lookup b r0 of
    Just xr -> unless (xr <= br) $ throwError $ sep ["Usage violation for", pretty name, "declared at", pretty loc, "expected", pretty br, "got", pretty xr ]
    Nothing -> error $ "panic: variable not found in usage: " <> (show b)
  modify (M.delete b)
  return x

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env     :: Env
                 , ctxt    :: Ctxt
                 , errCtx  :: [D]
                 , modules :: Modules
                 }

showCtxt :: Show a => [(([Char], t), a)] -> [Char]
showCtxt ctx = intercalate ", \n" $ reverse $ [i ++ " : " ++ show v | ((i,_),v) <- ctx]

logg :: D -> Typing a -> Typing a
logg x = local (\e -> e {errCtx = x:errCtx e})

oops :: D -> Typing a
oops msg = do
  TEnv {..} <- ask
  throwError $ sep [msg,
                    hang 2 "when:" (sep (map ((<> ":")) (reverse errCtx))),
                    hang 2 "in environment" (pretty env),
                    hang 2 "in context" (pretty ctxt)]

emptyEnv :: Modules -> TEnv
emptyEnv  = TEnv 0 Empty [] []

withLocal :: forall a. (Binder, Rig, Val) -> Typing a -> Typing a
withLocal (x,r,a') t = local (addTypeVal (x,a')) (checkUsage x r t)

addTypeVal :: (Binder, Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k rho gam ex ms) =
  TEnv (k+1) (Pair rho (x,mkVar k)) (p:gam) ex ms

addTeleVal :: VTele -> TEnv -> TEnv
addTeleVal VEmpty lenv = lenv
addTeleVal (VBind x _r a rest) lenv = addTypeVal (x,a) (addTeleVal (rest (mkVar (index lenv))) lenv) 

-- | Add a bunch of (already checked) declarations to the environment.
addDecls :: Recordoid -> TEnv -> TEnv
addDecls ([],VEmpty) = id
addDecls ((v:vs),VBind x _r a bs) = addDecls (vs,bs v) . addDecl x v a
addDecl x v a (TEnv k rho gam ex ms) = (TEnv k (Pair rho (x,v)) ((x,a):gam) ex) ms

trace :: D -> Typing ()
trace s = tell [s]

runTyping :: TEnv -> Typing a -> (Either D a,[D])
runTyping env (Typing t) = runWriter $ runExceptT $ runReaderT (fst <$> runStateT t zero) env

runModule :: TEnv -> Ter -> (ModuleState,[D])
runModule tenv e = first (either Failed (uncurry Loaded)) (runInfer tenv e)
  where first f (x,y) = (f x,y)

runInfer :: TEnv -> Ter -> (Either D (Val,Val),[D])
runInfer lenv t = runTyping lenv $ do
  (t',a) <- checkInfer t
  e <- asks env
  return (eval e t', a)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (CTer, Env)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> oops ("getLblType" <+> pretty c)
getLblType c u = oops (sep ["expected a data type for the constructor",
                              pretty c,"but got",pretty u])

getFresh :: Typing Val
getFresh = mkVar <$> index <$> ask


checkDecls :: TDecls () -> Typing (TDecls Val,Recordoid)
checkDecls (Open () r) = do
  (r',t) <- checkInfer r
  e <- asks env
  case t of
    VRecordT tele ->
      return (Open t r',(etaExpandRecord tele (eval e r'),tele))
    _ -> oops $ "attempt to open something which is not a record"
checkDecls (Mutual d) = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace (sep ["Checking: ", sep (map fromString idents)])
  tele' <- checkTele tele
  e <- asks env
  let vtele = evalTele e tele'
  ters' <- local (addTeleVal vtele) (checks vtele ters)
  let d' = zipWith (\(b,_r,ty) t -> (b,ty,t)) tele' ters'
  return (Mutual d',(map (eval (PDef (zip (map frst tele) ters') e)) ters', vtele)) -- allowing recursive definitions

frst (x,_,_) = x

checkDeclss :: [TDecls ()] -> Typing [(TDecls Val,Recordoid)]
checkDeclss [] = return []
checkDeclss (ds:dss) = do
  r@(_,(vs,tele)) <- checkDecls ds
  (r:) <$> local (addDecls (vs,tele)) (checkDeclss dss)

checkTele :: Tele () -> Typing (Tele Val)
checkTele []          = return []
checkTele ((x,r,a):xas) = do
  (aa,a') <- checkTypeEval a
  ((x,r,aa):) <$> local (addTypeVal (x,a')) (checkTele xas)


checkLogg :: Val -> Ter -> Typing CTer
checkLogg v t = logg (sep ["Checking that " <> pretty t, "has type " <> pretty v]) $ check v t

check :: Val -> Ter -> Typing CTer
check a t = case (a,t) of
  (_,Con c e) -> do
    (b,nu) <- getLblType c a
    Con c <$> check (eval nu b) e
  (VU,Sum loc bs) -> Sum loc <$> forM bs (\(l,a) -> (l,) <$> checkType a)
  (VPi x r (Ter (Sum _ cas) nu) f,Split loc ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then do Split loc <$>
                 (forM (zip ces' cas') $ \((lbl1,(bndr,term)), ((_lbl2,_),typ)) -> do
                     Lam _ _ term' <- check (VPi x r (eval nu typ) f) (Lam bndr Nothing term)
                     return (lbl1,(bndr,term')))
       else oops "case branches do not match the data type"
  (VPi _ r a f,Lam x aa t)  -> do
    var <- getFresh
    (a',aa') <- case aa of
      Just aaa -> do (aa',a') <- checkTypeEval aaa
                     checkSub "lam type" a' a
                     return (a',Just aa')
      Nothing -> return (a,Nothing)
    Lam x aa' <$> withLocal (x,r,a') (check (app f var) t)
  (VRecordT ts, Record fs) -> do
    Record <$> checkRecord ts fs
  (VMeet w v,_) -> check w t >> check v t
  -- (VJoin w v,_) -> check w t `catchError` \e1 ->
  --                  check v t `catchError` \e2 ->
  --                  throwError $ sep [e1,"AND",e2]
  -- Unfortunately we cannot use the above rule because then we cannot derive x:A∨B ⊢ x:A∨B
  (_,Where e d) -> do
    (dd,d') <- unzip <$> checkDeclss d
    e' <- local (addDecls (mconcat d')) $ check a e
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
checkRecord (VBind (x,l) rig a r) ts =
  case lookup x ts of
    Nothing -> oops $ sep ["type expects field", pretty x, "but it cannot be found in the term."]
    Just t -> do
      (tt,t') <- relax rig (checkEval a t)
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
        oops $ sep [msg <> pretty v, " is not a subtype of ", pretty a, "because " <> err]

checkType :: Ter -> Typing CTer
checkType t = do
  (t',a) <- relax zero (checkInfer t)
  case a of
   VU -> return t'
   _ -> oops $ sep ["expected a type, but got", pretty t, "which as type",pretty a]

unsafeInfer :: TEnv -> Ter -> Val
unsafeInfer e t = case (runInfer e t) of
  (Right (_,v),_) -> v

-- | Infer the type of the argument
checkInfer :: Ter -> Typing (CTer,Val)
checkInfer e = case e of
  Lam b@(x,_) (Just a) t -> do
    (aa,a') <- checkTypeEval a
    (tt,_) <- local (addTypeVal (b,a')) (checkInfer t)
    g <- ask
    return (Lam b (Just aa) tt, pi x a' (\v -> unsafeInfer (addDecl b v a' g) t))
  Import i () -> do
    ms <- asks modules
    case lookup i ms of
      Nothing -> throwError $ sep ["unknown module:", fromString i]
      Just (Failed d) -> throwError $ sep ["failed dependency: " <> fromString i,d]
      Just (Loaded val typ) -> do
        return (Import i val, typ)
  Module dclss -> do
    dss <- checkDeclss dclss
    let (_vals,tele) = mconcat [r | (Mutual _,r) <- dss]
    -- note: we do not re-rexport "opens"
    return (Module (map fst dss),VRecordT tele)
  Real x -> return (Real x, real)
  Prim p -> return (Prim p,lkPrimTy p)
  Pi x' rig a (Lam x _ b) -> do
    (aa,a') <- checkTypeEval a
    b' <- withLocal (x,zero,a') $ checkType b
    return (Pi x' rig aa (Lam x (Just aa) b' ),VU)
  RecordT [] -> return (RecordT [], VU)
  RecordT ((x,rig,a):as) -> do
    (aa,a') <- checkTypeEval a
    RecordT as' <- withLocal (x,zero,a') $ checkType (RecordT as)
    return (RecordT ((x,rig,aa):as'), VU)
  U -> return (U,VU)                 -- U : U
  Var n -> do
    gam <- ctxt <$> ask
    case lookupIdent n gam of
      Just (b,v)  -> use b >> return (Var n,v)
      Nothing -> oops $ pretty n <> " is not declared"
  App t u -> do
    (t',t'') <- checkInfer t
    (u',retTyp) <- checkInferApp u t''
    return (App t' u', retTyp)
  Proj l t -> do
    (t',a) <- relax (zero :.. one) (checkInfer t)
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
    (_,d') <- unzip <$> checkDeclss d
    local (addDecls (mconcat d')) $ checkInfer t
  _ -> oops ("checkInfer " <> pretty e)


checkInferApp :: Ter -> {- argument -}
                 Val -> {- function type -} Typing (CTer,Val)
checkInferApp u (VPi _ r a f) = do
   (u',u'') <- relax r (checkEval a u)
   return (u', app f u'')
checkInferApp u (VJoin x y) = do
  (u',typ1) <- checkInferApp u x
  (_ ,typ2) <- checkInferApp u y
  return (u',vJoin typ1 typ2)
checkInferApp u (VMeet x y) = do
  (u',typ1) <- checkInferApp u x `catchError` \_ -> checkInferApp u y
  (_ ,typ2) <- checkInferApp u y `catchError` \_ -> return (u',typ1)
  return (u',vMeet typ1 typ2)
checkInferApp _ c = oops $ pretty c <> " is not a product"

checkInferProj :: String -> {- ^ field to project-} Val -> {- ^ record value-} VTele -> {- ^ record type-} Typing Val
checkInferProj l _ VEmpty = oops $ "field not found:" <> pretty l
checkInferProj l r (VBind (x,_) _rig a rest)
  | x == l = return a
  | otherwise = checkInferProj l r (rest (projVal x r))
checkInferProj _ _ VBot = error "checkInferProj: VBot escaped from meet"

checks :: VTele -> [Ter] -> Typing [CTer]
checks _              []     = return []
checks (VBind _ rig v xas) (e:es) = do
  (ee,e') <- relax rig (checkEval v e)
  (ee:) <$> checks (xas e') es
checks _              _      = oops "checks"
