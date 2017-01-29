{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms, FlexibleContexts, RecordWildCards, OverloadedStrings, TypeSynonymInstances #-}
module TypeChecker where

import Data.Function
import Data.List
import Data.Monoid hiding (Sum)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except hiding (throwError)
import Control.Monad.Trans.Reader
import Control.Monad.Except
import Pretty

import TT
import Eval

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

-- instance Error D where
  
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

addType :: (Binder,Ter) -> TEnv -> Typing TEnv
addType (x,a) tenv@(TEnv _ rho _ _ _) = return $ addTypeVal (x,eval rho a) tenv

addC :: Ctxt -> (Tele,Env) -> [(Binder,Val)] -> Typing Ctxt
addC gam _             []          = return gam
addC gam ((y,a):as,nu) ((x,u):xus) = 
  addC ((x,eval nu a):gam) (as,Pair nu (y,u)) xus

addDecls :: Decls -> TEnv -> Typing TEnv
addDecls d (TEnv k rho gam ex v) = do
  let rho1 = PDef [ (x,y) | (x,_,y) <- d ] rho
      es' = evals rho1 (declDefs d)
  gam' <- addC gam (declTele d,rho) es'
  return $ TEnv k rho1 gam' ex v

addTele :: Tele -> TEnv -> Typing TEnv
addTele xas lenv = foldM (flip addType) lenv xas

trace :: String -> Typing ()
trace s = do
  b <- verbose <$> ask
  when b $ liftIO (putStrLn s)

runTyping :: TEnv -> Typing a -> IO (Either D a)
runTyping env t = runExceptT $ runReaderT t env

-- Used in the interaction loop
runDecls :: TEnv -> Decls -> IO (Either D TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  addDecls d tenv

runDeclss ::  TEnv -> [Decls] -> IO (Maybe D,TEnv)
runDeclss tenv []         = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either D Val)
runInfer lenv e = runTyping lenv (checkInfer e)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Ter, Env)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> oops ("getLblType" <+> pretty c)
getLblType c u = oops (sep ["expected a data type for the constructor",
                              pretty c,"but got",pretty u])

-- Useful monadic versions of functions:
localM :: (TEnv -> Typing TEnv) -> Typing a -> Typing a
localM f r = do
  e <- ask
  a <- f e
  local (const a) r

getFresh :: Typing Val
getFresh = mkVar <$> index <$> ask

checkDecls :: Decls -> Typing ()
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  rho <- asks env
  localM (addTele tele) $ checks (tele,rho) ters

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  inferType a
  localM (addType (x,a)) $ checkTele xas

checkLogg :: Val -> Ter -> Typing ()
checkLogg v t = logg (sep ["Checking that " <> pretty t, "has type " <> pretty v]) $ check v t

check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Con c e) -> do
    (b,nu) <- getLblType c a
    check (eval nu b) e
  (VU,Sum _ bs) -> sequence_ [checkType a | (_,a) <- bs]
  (VPi _ (Ter (Sum _ cas) nu) f,Split _ ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then sequence_ [ check (VPi "" (eval nu typ) f) (Lam bndr term)
                      | ((_lbl1,(bndr,term)), ((_lbl2,_),typ)) <- zip ces' cas' ]
       else oops "case branches does not match the data type"
  (VPi _ a f,Lam x t)  -> do
    var <- getFresh
    local (addTypeVal (x,a)) $ check (app f var) t
  (VRecordT ts, Record fs) -> do
    checkRecord ts fs
  (VMeet w v,_) -> check w t >> check v t
  (VJoin w v,_) -> check w t `catchError` \e1 ->
                   check v t `catchError` \e2 ->
                   throwError $ sep [e1,"AND",e2]
  (_,Where e d) -> do
    checkDecls d
    localM (addDecls d) $ check a e
  (_,Undef _) -> return ()
  _ -> do
    logg (sep ["Checking that" <+> pretty t, "has type" <+> pretty a]) $ do
       v <- checkInfer t
       checkSub "inferred type" a v

-- | Check that a record has a given type
checkRecord :: VTele -> [(String,Ter)] -> Typing ()
checkRecord VEmpty _ = return () -- other fields are ignored.
checkRecord (VBind x a r) ts =
  case lookup x ts of
    Nothing -> oops $ sep ["type expects field", pretty x, "but it cannot be found in the term."]
    Just t -> do
      t' <- checkEval a t
      checkRecord (r t') ts

checkEval :: Val -> Ter -> Typing Val
checkEval a t = do
  checkLogg a t
  eval' t

eval' :: Ter -> Typing Val
eval' t = do
  e <- asks env
  return $ eval e t

checkSub :: D -> Val -> Val -> Typing ()
checkSub msg a v = do
    k <- index <$> ask
    case sub k v a of
      Nothing -> return ()
      Just err -> do
        oops $ sep ["In" <+> msg, pretty v <> " is not a subtype of " <> pretty a, "because " <> err]

inferType :: Ter -> Typing Val
inferType t = do
  a <- checkInfer t
  case a of
   VU -> return a
   _ -> oops $ sep ["expected a type, but got", pretty t, "which as type",pretty a]


-- | Infer the type of the argument
checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  Real _ -> return real
  Prim p -> return $ lkPrimTy p
  Pi _ a (Lam x b) -> do
    _ <- inferType a
    localM (addType (x,a)) $ inferType b
  RecordT [] -> return VU
  RecordT ((x,a):as) -> do
    _ <- inferType a
    localM (addType (x,a)) $ inferType (RecordT as)
  U -> return VU                 -- U : U
  Var n -> do
    gam <- ctxt <$> ask
    case getIdent n gam of
      Just v  -> return v
      Nothing -> oops $ pretty n <> " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      VPi _ a f -> do
        checkLogg a u
        rho <- asks env
        let v = eval rho u
        return $ app f v
      _       -> oops $ pretty c <> " is not a product"
  Proj l t -> do
    a <- checkInfer t
    t' <- eval' t
    case a of
      VRecordT rt -> checkInferProj l t' rt
      _          -> oops $ pretty a <> " is not a record-type"
  Meet t u -> do
    _ <- inferType t
    _ <- inferType u
    return VU
  Join t u -> do
    _ <- inferType t
    _ <- inferType u
    return VU
  Where t d -> do
    checkDecls d
    localM (addDecls d) $ checkInfer t
  _ -> oops ("checkInfer " <> pretty e)

checkInferProj :: String -> {- ^ field to project-} Val -> {- ^ record value-} VTele -> {- ^ record type-} Typing Val
checkInferProj l _ VEmpty = oops $ "field not found:" <> pretty l
checkInferProj l r (VBind x a rest)
  | x == l = return a
  | otherwise = checkInferProj l r (rest (projVal x r))
checkInferProj _ _ VBot = error "checkInferProj: VBot escaped from meet"

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  let v = eval nu a
  check v e
  rho <- asks env
  let v' = eval rho e
  checks (xas,Pair nu (x,v')) es
checks _              _      = oops "checks"

checkType :: Ter -> Typing ()
checkType t = inferType t >> return ()
