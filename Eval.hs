{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}

module Eval where

import Prelude hiding (Num(..), pi)
import Pretty
import TT
import Data.Monoid hiding (Sum)
import Data.Dynamic
import Data.Maybe (fromJust)
import Algebra.Classes hiding (Sum)

-- | Lookup a value in the environment
look :: Ident -> Env -> (Binder, Val)
look x (Pair rho (n@(y,_l),u))
  | x == y    = (n, u)
  | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x r1
look x Empty = error ("panic: variable not found in env:" ++ show x)

etaExpandRecord :: VTele -> Val -> [Val]
etaExpandRecord VEmpty _ = []
etaExpandRecord (VBind (x,_) _rig  _ xs) r = let v = projVal x r in v:etaExpandRecord (xs v) r

evalDecls :: TDecls Val -> Env -> (Env,[(String,Val)])
evalDecls (Mutual decls) ρ = (ρ',[(x,eval ρ' y) | ((x,_),_,y) <- decls])
  where ρ' = PDef [ (x,y) | (x,_,y) <- decls ] ρ
evalDecls (Open (VRecordT tele) t) ρ = (foldl Pair ρ (zip (teleBinders tele) vs),[])
  where vs = etaExpandRecord tele (eval ρ t)

evalDeclss :: [TDecls Val] -> Env -> (Env,[(String,Val)])
evalDeclss dss ρ = foldl (\(e,vs) ds -> let (e',vs') = evalDecls ds e in (e',vs++vs')) (ρ,[]) dss

eval :: Env -> CTer -> Val
eval _ U               = VU
eval e (App r s)       = app (eval e r) (eval e s)
eval e (Var i)         = snd (look i e)
eval e (Pi nm r a b)     = VPi nm r (eval e a) (eval e b)
-- eval e (Lam x t)    = Ter (Lam x t) e -- stop at lambdas
eval e (Lam x _ t)       = VLam (fst x) $ \x' -> eval (Pair e (x,x')) t
eval e (RecordT bs)      = VRecordT $ evalTele e bs
eval e (Record fs)     = VRecord [(l,eval e x) | (l,x) <- fs]
eval e (Proj l a)        = projVal l (eval e a)
eval e (Where t decls) = eval (fst (evalDeclss decls e)) t
eval e (Module decls)  = VRecord (snd (evalDeclss decls e))
eval e (Con name ts)   = VCon name (eval e ts)
eval e (Split pr alts) = Ter (Split pr alts) e
eval e (Sum pr ntss)   = Ter (Sum pr ntss) e
eval _ (Undef x)       = VVar $ "<undefined: " ++ show x ++ " >"
eval _ (Real r)        = VPrim (toDyn r) (show r)
eval _ (Prim ('#':nm)) = VAbstract nm
eval _ (Prim nm)       = lkPrim nm
eval _ (Import _ v)    = v
eval e (Meet t u)      = vMeet (eval e t) (eval e u)
eval e (Join t u)      = vJoin (eval e t) (eval e u)
eval e (Singleton t u) = VSingleton (eval e t) (eval e u)

abstract :: String -> [Val] -> Val
abstract x = foldl app (VAbstract x)

binOp :: (Typeable a, Typeable b, Typeable c, Show c) =>
         (a -> b -> c) -> String -> Val
binOp op opName = VLam "x" $ \vx -> VLam "y" $ \vy -> case (vx,vy) of
  (VPrim (fromDynamic -> Just x) _, VPrim (fromDynamic -> Just y) _) ->
      let z = op x y
      in VPrim (toDyn z) (show z)
  _ -> abstract opName [vx,vy]

lkPrim :: String -> Val
lkPrim "-" = binOp ((-) :: Double -> Double -> Double) "-"
lkPrim "+" = binOp ((+) :: Double -> Double -> Double) "+"
lkPrim "*" = binOp ((*) :: Double -> Double -> Double) "*"
lkPrim "positive?" = VLam "x" $ \xi ->
                     VLam "type" $ \ty ->
                     VLam "true" $ \true ->
                     VLam "false" $ \false -> case xi of
  VPrim (fromDynamic -> Just (x::Double)) _ -> if x >= 0
                                               then true `app` (abstract "positive!" [xi])
                                               else false `app` VLam "neg" (\q -> -- the type system prevents getting here.
                                                             abstract "impossible" [q,(abstract "negative!" [xi])])
  _ -> abstract "positive?" [xi,ty,true,false]
lkPrim p = abstract p []

real :: Val
real = VAbstract "R"

positive :: Val -> Val
positive v = abstract ">=0" [v]

bot :: Val
bot = Ter (Sum (Loc "Props" (0,0)) []) Empty

infixr -->
(-->) :: Val -> Val -> Val
a --> b = pi "_" a $ \_ -> b
pi :: String -> Val -> (Val -> Val) -> Val
pi nm a f = VPi nm free a $ VLam nm f
lkPrimTy :: String -> Val
lkPrimTy "-" = real --> real --> real
lkPrimTy "+" = real --> real --> real
lkPrimTy "*" = real --> real --> real
lkPrimTy "positive?" = pi "x" real $ \x ->
                       pi "type" VU   $ \ty ->
                       (positive x --> ty) --> ((positive x --> bot) --> ty) --> ty
lkPrimTy "#R" = VU
lkPrimTy "#>=0" = real --> VU
lkPrimTy "#Ind" = VU
lkPrimTy p = error ("No type for primitive: " ++ show p)

evalTele :: Env -> Tele Val -> VTele
evalTele _ [] = VEmpty
evalTele e (((x,l),r,t):ts) = VBind (x,l) r t' (\x' -> evalTele (Pair e ((x,l),x')) ts)
  where t' = eval e t

vJoin :: Val -> Val -> Val
-- vJoin (VPi nm a b) (VPi _ a' b') = VPi nm (vMeet a a') (vJoin b b') -- EQUALITY of codomain is needed
vJoin (VRecordT fs) (VRecordT fs') | botTele x = VJoin (VRecordT fs) (VRecordT fs')
                                   | otherwise = VRecordT x
  where x = joinFields fs fs'
vJoin x y = VJoin x y

vMeet :: Val -> Val -> Val
vMeet (VRecordT fs) (VRecordT fs') | botTele x = VMeet (VRecordT fs) (VRecordT fs')
                                   | otherwise = VRecordT x
  where x = meetFields fs fs'
-- vMeet (VPi nm a b) (VPi _ a' b') = VPi nm (vJoin a a') (vMeet b b') -- EQUALITY of codomain is needed
vMeet x y = case conv 0 x y of
              Nothing -> x
              Just _ -> VMeet x y

hasField :: String -> VTele -> Bool
hasField l fs = l `elem` (map fst (teleBinders fs))

lacksField :: String -> VTele -> Bool
lacksField l fs = not (hasField l fs)

-- | Is this a bottom telescope?
botTele :: VTele -> Bool
botTele VEmpty = False
botTele VBot = True
botTele  (VBind _ _ _ t) = botTele (t (error "botTele: cannot look at values!"))

-- | the meet of two telescopes
meetFields :: VTele -> VTele -> VTele
meetFields VEmpty fs = fs
meetFields fs VEmpty = fs
meetFields fs@(VBind (l,ll) r a t) fs'@(VBind (l',ll') r' a' t')
  | l == l' = VBind (l,ll) (r /\ r') (vMeet a a') (\x -> meetFields (t x) (t' x))
  | lacksField l' fs  = VBind (l',ll') r' a' (\x -> meetFields fs (t' x))
  | lacksField l  fs' = VBind (l,ll)   r  a  (\x -> meetFields fs' (t x))
  | otherwise = VBot
meetFields VBot _ = VBot
meetFields _ VBot = VBot

-- | the join of two telescopes
joinFields :: VTele -> VTele -> VTele
joinFields VEmpty _ = VEmpty
joinFields _ VEmpty = VEmpty
joinFields fs@(VBind (l,ll) r a t) fs'@(VBind (l',_ll') r' a' t')
  | "__REMOVE__" `occursIn` a = joinFields (t remove) fs'
  | "__REMOVE__" `occursIn` a' = joinFields fs (t' remove)
  | l == l' = VBind (l,ll) (r \/ r') (vJoin a a') (\x -> joinFields (t x) (t' x))
  | lacksField l' fs  = joinFields fs (t' remove)
  | lacksField l  fs' = joinFields fs' (t remove)
  | otherwise = VBot
 where remove = VVar "__REMOVE__"
joinFields VBot _ = VBot
joinFields _ VBot = VBot

app :: Val -> Val -> Val
app (VLam _ f) u = f u
-- app (Ter (Lam cs x t) e) u = eval (Pair e (x,u)) t
app (Ter (Split _ nvs) e) (VCon name u) = case lookup name nvs of
    Just (x,t) -> eval (Pair e (x,u)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _) v | isNeutral v = VSplit u v -- v should be neutral
                            | otherwise   = error $ "app: VSplit " ++ show v
                                                  ++ " is not neutral"
app r s | isNeutral r = VApp r s -- r should be neutral
        | otherwise   = error $ "app: VApp " ++ show r ++ " is not neutral"


evals :: Env -> [(Binder,CTer)] -> [(Binder,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

projVal :: String -> Val -> Val
projVal l (VRecord fs)    = case lookup l fs of
  Just x -> x
  Nothing -> error $ "projVal: could not find field " ++ show l
projVal l u | isNeutral u = VProj l u
            | otherwise   = error $ show u ++ " should be neutral"

convs :: Int -> [Val] -> [Val] -> Maybe D
convs k a b = mconcat $ zipWith (conv k) a b

satisfy :: forall a. Bool -> a -> Maybe a
satisfy p err = if p then Nothing else Just err

equal :: (Pretty a, Eq a) => a -> a -> Maybe D
equal a b = satisfy (a == b) (fromJust $ different a b)

included :: (Pretty a, Ord a) => a -> a -> Maybe D
included a b = satisfy (a <= b) (sep [pretty a,"⊈",pretty b])

different :: (Pretty a) => a -> a -> Maybe D
different a b = Just (sep [pretty a,"≠",pretty b])

noSub :: (Pretty a2, Pretty a, Pretty a1) =>
               a2 -> a1 -> a -> Maybe D
noSub z a b = Just $ sep [pretty a,"not a subtype of",pretty b,"when inhabitant is",pretty z]

-- | @conv k a b@ Checks that @a@ can be converted to @b@.
conv :: Int -> Val -> Val -> Maybe D
conv _ VU VU = Nothing
conv k (VSingleton t v) (VSingleton t' v') = conv k t t' <> conv k v v'
conv k (VLam _ f) (VLam _ g) = do
  let v = mkVar k
  conv (k+1) (f v) (g v)
conv k (VLam _ f) g = do
  let v = mkVar k
  conv (k+1) (f v) (app g v)
conv k f (VLam _ g) = do
  let v = mkVar k
  conv (k+1) (app f v) (g v)
conv k (Ter (Lam x _ u) e) (Ter (Lam x' _ u') e') = do
  let v = mkVar k
  conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
conv k (Ter (Lam x _ u) e) u' = do
  let v = mkVar k
  conv (k+1) (eval (Pair e (x,v)) u) (app u' v)
conv k u' (Ter (Lam x _ u) e) = do
  let v = mkVar k
  conv (k+1) (app u' v) (eval (Pair e (x,v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p `equal` p') <> convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p `equal` p') <> convEnv k e e'
conv k (Ter (Undef p) e) (Ter (Undef p') e') =
  (p `equal` p') <> convEnv k e e'
conv k (VPi _ r u v) (VPi _ r' u' v') = do
  let w = mkVar k
  equal r r' <> conv k u' u  <> conv (k+1) (app v w) (app v' w)
conv k (VRecordT fs) (VRecordT fs') = 
  convTele k fs fs'
conv k (VProj l u) (VProj l' u') = equal l l' <> conv k u u'
conv k (VCon c us) (VCon c' us') =
  (c `equal` c') <> (conv k us us')
conv k (VRecord fs) (VRecord fs') = convFields k fs fs'
conv k (VApp u v)   (VApp u' v')   = conv k u u' <> conv k v v'
conv k (VSplit u v) (VSplit u' v') = conv k u u' <> conv k v v'
conv _ (VVar x)     (VVar x')      = x `equal` x'
conv _ (VAbstract n) (VAbstract n') = n `equal` n'
conv k (VJoin a b) (VJoin a' b') = (conv k a a' <> conv k b b') `orElse` (conv k a b' <> conv k b a')
conv k (VMeet a b) (VMeet a' b') = (conv k a a' <> conv k b b') `orElse` (conv k a b' <> conv k b a')
conv _ (VPrim _ _) (VPrim _ _) = Nothing
conv _ x              x'           = different x x'

-- -- @sub _ x:a b@: check that x:a also has type b.
sub :: Int -> Val -> Val -> Val -> Maybe D
sub _ _ VU VU = Nothing
sub k f (VPi _ r u v) (VPi _ r' u' v') = do
  let w = mkVar k
  included r' r <> sub k w u' u  <> sub (k+1) (app f w) (app v w) (app v' w)
sub k z (VRecordT fs) (VRecordT fs') = subTele k z fs fs'
sub k x (VJoin a b) c = sub k x a c <> sub k x b c
sub k x c (VJoin a b) = sub k x c a `orElse` sub k x c b
sub k x c (VMeet a b) = sub k x c a <> sub k x c b
sub k x (VMeet a b) c = sub k x a c `orElse` sub k x b c
sub k x (VSingleton t v) t' = sub k x t t' `orElse` sub k v t t'
sub k x t (VSingleton t' v') = sub k x t t' <> conv k x v'
sub k _ x x' = conv k x x'


orElse :: Maybe D -> Maybe D -> Maybe D
orElse Nothing _ = Nothing
orElse _ Nothing = Nothing
orElse (Just x) (Just y) = Just (x <> " and " <> y)

convEnv :: Int -> Env -> Env -> Maybe D
convEnv k e e' = mconcat $ zipWith (conv k) (valOfEnv e) (valOfEnv e')

convTele :: Int -> VTele -> VTele -> Maybe D
convTele _ VEmpty VEmpty = Nothing
convTele k (VBind (l,_) r a t) (VBind (l',_) r' a' t') = do
  let v = mkVar k
  equal r r' <> equal l l' <> conv k a a' <> convTele (k+1) (t v) (t' v)
convTele _ x x' = different x x'

subTele :: Int -> Val -> VTele -> VTele -> Maybe D
subTele _ _ _ VEmpty = Nothing  -- all records are a subrecord of the empty record
subTele k z (VBind (l,_ll) r a t) (VBind (l',ll') r' a' t') = do
  let v = projVal l z
  if l == l'
    then included r r' <> sub k v a a' <> subTele (k+1) z (t v) (t' v)
    else subTele (k+1) z (t v) (VBind (l',ll') r' a' t')
subTele _ z x x' = noSub z x x'
-- FIXME: Subtyping of records isn't complete. To be complete, one
-- would have to create a graph representation of the dependencies in
-- a record, and then check the covering of the graphs.

convFields :: Int -> [(String,Val)] -> [(String,Val)] -> Maybe D
convFields _ [] [] = Nothing
convFields k ((l,u):fs) ((l',u'):fs') = equal l l' <> conv k u u' <> convFields k fs fs'
convFields _ x x' = different x x'


--------------------
instance Pretty Val where pretty = showVal 0

showVal :: Int -> Val -> D
showVal ctx t0 = case t0 of
  VU            -> "Type"
  (VJoin u v)  -> pp 2 (\p -> p u <+> "\\/" <+> p v)
  (VMeet u v)  -> pp 3 (\p -> p u <+> "/\\" <+> p v)
  (Ter t env)  -> showTer ctx env t
  (VCon c us)  -> prn 4 (hang 2 ("`" <> pretty c) (showVal 5 us))
  (VPi nm r a f) -> pp 1 $ \p ->
     if dependent f then withVar nm $ \v -> (parens (pretty v <+> prettyBind r <+> pretty a) <+> "->") </> p (f `app` (VVar v))
     else (showVal 2 a  <+> "->") </> p (f `app` (VVar "_"))
  (VApp _ _)   -> pp 4 (\p -> hang 2 (p u) (showArgs vs))
     where (u:vs) = fnArgs t0
  (VSplit (Ter (Split _ branches) env) v) -> hang 2 ("case" <+> pretty v <+> "of") (showSplitBranches env branches)
  (VVar x)     -> pretty x
  (VRecordT tele) -> pretty tele
  (VRecord fs)   -> tupled [hang 2 (pretty l <> " =") (pretty e) | (l,e) <- fs]
  (VProj f u)     -> pp 5 (\p -> p u <> "." <> pretty f)
  (VLam nm f)  -> pp 1 $ \p -> withVar nm $ \v ->
    hang 0 ("\\" <> pretty v <+> "->") (p (f $ VVar v))
  (VPrim _ nm) -> pretty nm
  (VAbstract nm) -> pretty ('#':nm)
  (VSingleton t v) -> pretty t <> "(= " <> pretty v <> ")"
 where pp :: Int -> ((Val -> D) -> D) -> D
       pp opPrec k = prn opPrec (k (showVal opPrec))
       prn opPrec = (if opPrec < ctx then parens else id)

fnArgs (VApp u v) = fnArgs u ++ [v]
fnArgs x = [x]

occursIn :: forall v. Value v => String -> v -> Bool
x `occursIn` a = x `elem` unknowns a
dependent :: Val -> Bool
dependent f =  "__DEPENDS?__" `occursIn` (f `app` VVar "__DEPENDS?__")

showArgs :: [Val] -> D
showArgs = sep . map (showVal 5)


instance Show Val where
  show = render . pretty

prettyLook :: Ident -> Env -> D
prettyLook x (Pair rho (n@(y,_l),u))
  | x == y    = pretty u
  | otherwise = prettyLook x rho
prettyLook x (PDef es r1) = case lookupIdent x es of
  Just ((y,_loc),_t)  -> pretty y --  <> "[DEF]"
  Nothing ->   prettyLook x r1
prettyLook x Empty = pretty x {- typically bound in a Split -}


prettyTele :: VTele -> [D]
prettyTele VEmpty = []
prettyTele (VBind (nm,_l) r ty rest) = (pretty nm <+> prettyBind r <+> pretty ty) : prettyTele (rest $ VVar nm)

prettyBind :: Rig -> D
prettyBind (Fin 0 :.. Inf) = ":"
prettyBind r = ":" <> pretty r

instance Pretty VTele where
  pretty = encloseSep "[" "]" ";" . prettyTele

instance Pretty Env where
  pretty e = encloseSep "(" ")" ";" (showEnv e)

showEnv :: Env -> [D]
showEnv e0 = case e0 of
    Empty            -> []
    (PDef _xas env)   -> showEnv env
    (Pair env ((x,_),u)) -> (hang 2 (pretty x <+> "=") (pretty u)) : showEnv env

instance Pretty (Ter' a) where
  pretty = showTer 0 Empty

showTele :: Env -> Tele a -> [D]
showTele _ [] = mempty
showTele ρ (((x,_loc),r,t):tele) = (pretty x <+> prettyBind r <+> showTer 0 ρ t) : showTele ρ tele

showTer :: Int -> Env -> Ter' a -> D
showTer ctx ρ t0 = case t0 of
   Import i _    -> sep ["import",pretty i]
   Module ds     -> hang 2 "module"  (vcat (map (showDecls ρ) ds))
   U             -> "U"
   (Meet e0 e1)  -> pp 2 $ \p -> p e0 <+> "/\\" <+> p e1
   (Join e0 e1)  -> pp 2 $ \p -> p e0 <+> "\\/" <+> p e1
   (App _ _)   -> pp 4 $ \p -> p e0 <+> showTersArgs ρ es
     where (e0:es) = fnArgsTer t0
   (Pi _ r a (Lam ("_",_) _ t)) -> pp 1 $ \p -> (showTer 2 ρ a <+> "->") </> p t
   (Pi _ r a (Lam x _ t)) -> pp 1 $ \p -> (parens (pretty x <+> prettyBind r <+> showTer 0 ρ a) <+> "->") </> p t
   (Pi _ r e0 e1)    -> "Pi" <+> showTersArgs ρ [e0,e1]
   (Lam (x,_) _ e) -> pp 2 (\p -> hang 0 ("\\" <> pretty x <+> "->") (p e))
   (Proj l e)    -> pp 5 (\p -> p e <> "." <> pretty l)
   (RecordT ts)  -> encloseSep "[" "]" ";" (showTele ρ ts)
   (Record fs)   -> encloseSep "(" ")" "," [hang 2 (pretty l <> " =") (showTer 0 ρ e) | (l,e) <- fs]
   (Where e d)   -> pp 0 (\p -> hang 2 (p e) (hang 2 "where" (vcat $ map (showDecls ρ) d)))
   (Var x)       -> prettyLook x ρ
   (Con c es)    -> hang 2 ("`" <> pretty c) (showTer 5 ρ es)
   (Split _l branches)   -> hang 2 "split" (showSplitBranches ρ branches)
   (Sum _l branches) -> encloseSep "{" "}" "|" (map (showBranch ρ) branches)
   (Undef _)     -> "undefined (1)"
   (Real r)      -> showy r
   (Prim n)      -> showy n
   (Singleton t v) -> showTer ctx ρ t <> "(= " <> showTer 0 ρ v <> ")"
 where pp :: Int -> ((Ter' a -> D) -> D) -> D
       pp opPrec k = prn opPrec (k (showTer opPrec ρ))
       prn opPrec = (if opPrec < ctx then parens else id)

fnArgsTer (App u v) = fnArgsTer u ++ [v]
fnArgsTer x = [x]

showSplitBranches :: Env -> [Brc a] -> D
showSplitBranches ρ branches = encloseSep "{" "}" ";"
  [hang 2 (pretty l <+> ((pretty . fst) bnds) <+> "↦") (showTer 0 ρ t)  | (l,(bnds,t)) <- branches]

showBranch :: Env -> (Binder, Ter' a) -> D
showBranch env ((b,_),arg) = pretty b <+> (showTer 0 env arg)

instance Pretty Ctxt where
  pretty ctxt = vcat [pretty nm <+> ":" <+> pretty typ | ((nm,_),typ) <- ctxt]

showTersArgs :: Env -> [Ter' a] -> D
showTersArgs ρ = sep . map (showTer 5 ρ)

showDecl :: Pretty a => Env -> (a, Ter' b, Ter' b) -> D
showDecl ρ (b,typ,ter) = vcat [pretty b <+> ":" <+> showTer 0 ρ typ,
                               pretty b <+> "=" <+> showTer 0 ρ ter]

showDecls :: Env -> TDecls a -> D
showDecls ρ (Open _ x) = "open " <> showTer 0 ρ x
showDecls ρ (Mutual defs) = vcat (map (showDecl ρ) defs)

class Value v where
  unknowns :: v -> [String] -- aka "free variables"

instance Value Val where
  unknowns v0 = case v0 of
    VU -> []
    VPi _binder _rig x  y -> unknowns x ++ unknowns y
    VRecordT x -> unknowns x
    VRecord x -> concatMap (unknowns . snd) x
    VCon _ x -> unknowns x
    VApp x y -> unknowns x ++ unknowns y
    VSplit x y -> unknowns x ++ unknowns y
    VProj _ x -> unknowns x
    VLam _ f -> unknowns (f (VVar "___UNK___"))
    VPrim{} -> []
    VAbstract{} -> []
    VMeet x y -> unknowns x ++ unknowns y
    VJoin x y -> unknowns x ++ unknowns y
    VVar x -> [x]
    Ter _ env -> unknowns env
    VSingleton t u -> unknowns t ++ unknowns u

instance Value Env where
  unknowns Empty = []
  unknowns (Pair env (_,u)) = unknowns env ++ unknowns u
  unknowns (PDef _ env) = unknowns env

instance Value VTele where
  unknowns VEmpty = []
  unknowns (VBind _binder _rig x y) = unknowns x ++ unknowns (y (VVar "___UNK___"))
  unknowns VBot = []

deriving instance  Show ModuleState
