{-# LANGUAGE PatternSynonyms, FlexibleContexts, RecordWildCards #-}
module TypeChecker where

import Data.Either
import Data.Function
import Data.List
import Data.Maybe
import Data.Monoid hiding (Sum)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Trans.Reader
import Control.Monad.Error (throwError)
import Control.Applicative
import Pretty

import TT
import Eval

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String IO) a

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env     :: Env
                 , ctxt    :: Ctxt
                 , errCtx  :: [String]
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }
  deriving (Show)

showCtxt :: Show a => [(([Char], t), a)] -> [Char]
showCtxt ctx = intercalate ", \n" $ reverse $ [i ++ " : " ++ show v | ((i,_),v) <- ctx]

logg :: String -> Typing a -> Typing a
logg x = local (\e -> e {errCtx = x:errCtx e})

oops :: String -> Typing a
oops msg = do
  TEnv {..} <- ask
  throwError ("In:\n" ++ concatMap (++ ":\n") (reverse errCtx) ++ msg ++ "\n in environment" ++ show env ++ "\n in context\n" ++ showCtxt ctxt )

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

addBranch :: [(Binder,Val)] -> (Tele,Env) -> TEnv -> Typing TEnv
addBranch nvs (tele,env) (TEnv k rho gam ex v) = do
  e <- addC gam (tele,env) nvs
  return $ TEnv (k + length nvs) (upds rho nvs) e ex v

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

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runErrorT $ runReaderT t env

-- Used in the interaction loop
runDecls :: TEnv -> Decls -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  addDecls d tenv

runDeclss :: TEnv -> [Decls] -> IO (Maybe String,TEnv)
runDeclss tenv []         = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (checkInfer e)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> oops ("getLblType " ++ show c)
getLblType c u = oops ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

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
checkLogg v t = logg ("Checking that " ++ show t ++ " has type " ++ show v) $ check v t

check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) nu) f,Split _ ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces' cas' ]
       else oops "case branches does not match the data type"
  (VPi a f,Lam x t)  -> do
    var <- getFresh
    rho <- asks env
    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, SPair t1 t2) -> do
    v <- checkEval a t1
    check (app f v) t2
  (_,Where e d) -> do
    checkDecls d
    localM (addDecls d) $ check a e
  (_,Undef _) -> return ()
  _ -> do
    logg ("checking that term " ++ show t ++ " has type " ++ show a) $ do
       v <- checkInfer t
       checkConv "inferred type" a v


arrs :: [Val] -> Val -> Val
arrs [] t = t
arrs (a:as) t = VPi a $ VLam $ \_ -> arrs as t
  
checkEval :: Val -> Ter -> Typing Val
checkEval a t = do
  checkLogg a t
  eval' t

eval' :: Ter -> Typing Val
eval' t = do
  e <- asks env
  return $ eval e t

checkConvs :: String -> [Val] -> [Val] -> Typing ()
checkConvs msg a v = sequence_ [checkConv msg a' v' | (a',v') <- zip a v]
  
checkConv msg a v = do
    k <- index <$> ask
    case conv k v a of
      Nothing -> return ()
      Just err -> do
      rho <- asks env
      oops $ msg ++ " check conv: \n  " ++ show v ++ " /= " ++ show a ++ "\n because  " ++ err

checkBranch :: (Tele,Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k   <- asks index
  env <- asks env
  let l  = length xas
      us = map mkVar [k..k+l-1]
  localM (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e

inferType :: Ter -> Typing Val
inferType t = do
  a <- checkInfer t
  case a of
   VU -> return a
   _ -> oops $ show a ++ " is not a type"

checkInfer :: Ter -> Typing Val
checkInfer e = case e of
  Pi a (Lam x b) -> do
    inferType a
    localM (addType (x,a)) $ inferType b
  Sigma a (Lam x b) -> do
    inferType a
    localM (addType (x,a)) $ inferType b
  U -> return VU                 -- U : U
  Var n -> do
    gam <- ctxt <$> ask
    case getIdent n gam of
      Just v  -> return v
      Nothing -> oops $ show n ++ " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      VPi a f -> do
        checkLogg a u
        rho <- asks env
        let v = eval rho u
        return $ app f v
      _       -> oops $ show c ++ " is not a product"
  Fst t -> do
    c <- checkInfer t
    case c of
      VSigma a f -> return a
      _          -> oops $ show c ++ " is not a sigma-type"
  Snd t -> do
    c <- checkInfer t
    case c of
      VSigma a f -> do
        e <- asks env
        let v = eval e t
        return $ app f (fstSVal v)
      _          -> oops $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    localM (addDecls d) $ checkInfer t
  _ -> oops ("checkInfer " ++ show e)

extractFun :: Int -> Val -> Typing ([Val],Val)
extractFun 0 a = return ([],a)
extractFun n (VPi a f) = do
  (as,b) <- extractFun (n-1) (f `app` VVar "extractFun")
  return (a:as,b)

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  let v = eval nu a
  check v e
  rho <- asks env
  let v' = eval rho e
  checks (xas,Pair nu (x,v')) es
checks _              _      = oops "checks"

-- Not used since we have U : U
--
-- (=?=) :: Typing Ter -> Ter -> Typing ()
-- m =?= s2 = do
--   s1 <- m
--   unless (s1 == s2) $ oops (show s1 ++ " =/= " ++ show s2)
--
-- checkTs :: [(String,Ter)] -> Typing ()
-- checkTs [] = return ()
-- checkTs ((x,a):xas) = do
--   checkType a
--   local (addType (x,a)) (checkTs xas)
--
-- checkType :: Ter -> Typing ()
-- checkType t = case t of
--   U              -> return ()
--   Pi a (Lam x b) -> do
--     checkType a
--     local (addType (x,a)) (checkType b)
--   _ -> checkInfer t =?= U
