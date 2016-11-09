{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
module Eval where

import TT
import Control.Applicative
import Data.Monoid hiding (Sum)

look :: Ident -> Env -> (Binder, Val)
look x (Pair rho (n@(y,_l),u))
  | x == y    = (n, u)
  | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x r1


eval :: Env -> Ter -> Val
eval _ U               = VU
eval e (App r s)       = app (eval e r) (eval e s)
eval e (Var i)         = snd (look i e)
eval e (Pi a b)        = VPi (eval e a) (eval e b)
-- eval e (Lam is x t)    = Ter (Lam is x t) e -- stop at lambdas
eval e (Lam x t)       = VLam $ \x' -> eval (Pair e (x,x')) t
eval e (RecordT bs)      = VRecordT $ evalTele e bs
eval e (Record fs)     = VRecord [(l,eval e x) | (l,x) <- fs]
eval e (Proj l a)        = projVal l (eval e a)
eval e (Where t decls) = eval (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval e (Con name ts)   = VCon name (map (eval e) ts)
eval e (Split pr alts) = Ter (Split pr alts) e
eval e (Sum pr ntss)   = Ter (Sum pr ntss) e
eval _ (Undef _)       = error "undefined (2)"

evalTele :: Env -> Tele -> VTele
evalTele _ [] = VEmpty
evalTele e (((x,l),t):ts) = VBind x t' (\x' -> evalTele (Pair e ((x,l),x')) ts)
  where t' = eval e t

app :: Val -> Val -> Val
app (VLam f) u = f u
-- app (Ter (Lam cs x t) e) u = eval (Pair e (x,clams cs u)) t
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t) -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _) v | isNeutral v = VSplit u v -- v should be neutral
                            | otherwise   = error $ "app: VSplit " ++ show v
                                                  ++ " is not neutral"
app r s | isNeutral r = VApp r s -- r should be neutral
        | otherwise   = error $ "app: VApp " ++ show r ++ " is not neutral"


evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

second :: (t -> t2) -> (t1, t) -> (t1, t2)
second f (a,b) = (a, f b)

projVal :: String -> Val -> Val
projVal l (VRecord fs)    = case lookup l fs of
  Just x -> x
  Nothing -> error $ "projVal: could not find field " ++ show l
projVal l u | isNeutral u = VProj l u
            | otherwise   = error $ show u ++ " should be neutral"

convs :: Int -> [Val] -> [Val] -> Maybe String
convs k a b = mconcat $ zipWith (conv k) a b

equal :: (Show a, Eq a) => a -> a -> Maybe [Char]
equal a b | a == b = Nothing
          | otherwise = different a b

different :: (Show a) => a -> a -> Maybe [Char]
different a b = Just $ show a ++ " /= " ++ show b

conv :: Int -> Val -> Val -> Maybe String
conv _ VU VU = Nothing
conv k (VLam f) (VLam g) = do
  let v = mkVar k
  conv (k+1) (f v) (g v)
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') = do
  let v = mkVar k
  conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
conv k (Ter (Lam x u) e) u' = do
  let v = mkVar k
  conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
conv k u' (Ter (Lam x u) e) = do
  let v = mkVar k
  conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p `equal` p') <> convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p `equal` p') <> convEnv k e e'
conv k (Ter (Undef p) e) (Ter (Undef p') e') =
  (p `equal` p') <> convEnv k e e'
conv k (VPi u v) (VPi u' v') = do
  let w = mkVar k
  conv k u u' <> conv (k+1) (app v w) (app v' w)
conv k (VRecordT fs) (VRecordT fs') = 
  convTele k fs fs'
conv k (VProj l u) (VProj l' u') = equal l l' <> conv k u u'
conv k (VCon c us) (VCon c' us') =
  (c `equal` c') <> mconcat (zipWith (conv k) us us')
conv k (VRecord fs) (VRecord fs') = convFields k fs fs'
conv k (VApp u v)   (VApp u' v')   = conv k u u' <> conv k v v'
conv k (VSplit u v) (VSplit u' v') = conv k u u' <> conv k v v'
conv _ (VVar x)     (VVar x')      = x `equal` x'
conv _ x              x'           = different x x'

convEnv :: Int -> Env -> Env -> Maybe String
convEnv k e e' = mconcat $ zipWith (conv k) (valOfEnv e) (valOfEnv e')


convTele :: Int -> VTele -> VTele -> Maybe String
convTele _ VEmpty VEmpty = Nothing
convTele k (VBind l a t) (VBind l' a' t') = do
  let v = mkVar k
  equal l l' <> conv k a a' <> convTele (k+1) (t v) (t' v)
convTele _ x x' = different x x'


convFields :: Int -> [(String,Val)] -> [(String,Val)] -> Maybe String
convFields _ [] [] = Nothing
convFields k ((l,u):fs) ((l',u'):fs') = equal l l' <> conv k u u' <> convFields k fs fs'
convFields _ x x' = different x x'
