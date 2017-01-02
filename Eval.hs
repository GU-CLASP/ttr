{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
module Eval where

import Pretty
import TT
import Data.Monoid hiding (Sum)
import Data.Dynamic
import Prelude hiding (pi)

-- | Lookup a value in the environment
look :: Ident -> Env -> (Binder, Val)
look x (Pair rho (n@(y,_l),u))
  | x == y    = (n, u)
  | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x r1
look _ Empty = error "panic: variable not found in env"


eval :: Env -> Ter -> Val
eval _ U               = VU
eval e (App r s)       = app (eval e r) (eval e s)
eval e (Var i)         = snd (look i e)
eval e (Pi a b)        = VPi (eval e a) (eval e b)
-- eval e (Lam x t)    = Ter (Lam x t) e -- stop at lambdas
eval e (Lam x t)       = VLam $ \x' -> eval (Pair e (x,x')) t
eval e (RecordT bs)      = VRecordT $ evalTele e bs
eval e (Record fs)     = VRecord [(l,eval e x) | (l,x) <- fs]
eval e (Proj l a)        = projVal l (eval e a)
eval e (Where t decls) = eval (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval e (Con name ts)   = VCon name (map (eval e) ts)
eval e (Split pr alts) = Ter (Split pr alts) e
eval e (Sum pr ntss)   = Ter (Sum pr ntss) e
eval _ (Undef _)       = error "undefined (2)"
eval _ (Real r)        = VPrim (toDyn r) (show r)
eval _ (Prim ('#':nm)) = VAbstract nm
eval _ (Prim nm)       = lkPrim nm
eval e (Meet t u)      = vMeet (eval e t) (eval e u)
eval e (Join t u)      = vJoin (eval e t) (eval e u)

abstract :: String -> [Val] -> Val
abstract x = foldl app (VAbstract x)

binOp :: (Typeable a, Typeable b, Typeable c, Show c) =>
         (a -> b -> c) -> String -> Val
binOp op opName = VLam $ \vx -> VLam $ \vy -> case (vx,vy) of
  (VPrim (fromDynamic -> Just x) _, VPrim (fromDynamic -> Just y) _) ->
      let z = op x y
      in VPrim (toDyn z) (show z)
  _ -> abstract opName [vx,vy]

lkPrim :: String -> Val
lkPrim "-" = binOp ((-) :: Double -> Double -> Double) "-"
lkPrim "+" = binOp ((+) :: Double -> Double -> Double) "+"
lkPrim "*" = binOp ((*) :: Double -> Double -> Double) "*"
lkPrim "positive?" = VLam $ \xi ->
                     VLam $ \ty ->
                     VLam $ \true ->
                     VLam $ \false -> case xi of
  VPrim (fromDynamic -> Just (x::Double)) _ -> if x >= 0
                                               then true `app` (abstract "positive!" [xi])
                                               else false `app` VLam (\q -> -- the type system prevents getting here.
                                                             abstract "impossible" [q,(abstract "negative!" [xi])])
  _ -> abstract "positive?" [xi,ty,true,false]
lkPrim p = abstract p []

real :: Val
real = VAbstract "R"

positive :: Val -> Val
positive v = abstract ">0" [v]

bot :: Val
bot = Ter (Sum ("Bot",Loc "Props" (4,6)) []) Empty

infixr -->
(-->) :: Val -> Val -> Val
a --> b = pi a $ \_ -> b
pi :: Val -> (Val -> Val) -> Val
pi a f = VPi a $ VLam f
lkPrimTy :: String -> Val
lkPrimTy "-" = real --> real --> real
lkPrimTy "+" = real --> real --> real
lkPrimTy "*" = real --> real --> real
lkPrimTy "positive?" = pi real $ \x ->
                       pi VU   $ \ty ->
                       (positive x --> ty) --> ((positive x --> bot) --> ty) --> ty
lkPrimTy "#R" = VU
lkPrimTy "#>=0" = real --> VU
lkPrimTy "#Ind" = VU
lkPrimTy p = error ("No type for primitive: " ++ show p)

evalTele :: Env -> Tele -> VTele
evalTele _ [] = VEmpty
evalTele e (((x,l),t):ts) = VBind x t' (\x' -> evalTele (Pair e ((x,l),x')) ts)
  where t' = eval e t

vJoin :: Val -> Val -> Val
vJoin = VJoin

vMeet :: Val -> Val -> Val
vMeet (VRecordT fs) (VRecordT fs') | botTele x = VMeet (VRecordT fs) (VRecordT fs')
                                   | otherwise = VRecordT x
  where x = meetFields fs fs'
vMeet x y = VMeet x y

hasField :: String -> VTele -> Bool
hasField _ VEmpty = False
hasField l (VBind l' _ t) = l == l' || hasField l (t (error "hasField: cannot look at values!"))
hasField _ VBot = error "VBot escaped from meet"

lacksField :: String -> VTele -> Bool
lacksField l fs = not (hasField l fs)

-- | Is this a bottom telescope?
botTele :: VTele -> Bool
botTele VEmpty = False
botTele VBot = True
botTele  (VBind _ _ t) = botTele (t (error "botTele: cannot look at values!"))

-- | the meet of two telescopes
meetFields :: VTele -> VTele -> VTele
meetFields VEmpty fs = fs
meetFields fs VEmpty = fs
meetFields fs@(VBind l a t) fs'@(VBind l' a' t')
  | l == l' = VBind l (vMeet a a') (\x -> meetFields (t x) (t' x))
  | lacksField l' fs  = VBind l' a' (\x -> meetFields fs (t' x))
  | lacksField l  fs' = VBind l  a  (\x -> meetFields fs' (t x))
  | otherwise = VBot
meetFields VBot _ = VBot
meetFields _ VBot = VBot

app :: Val -> Val -> Val
app (VLam f) u = f u
-- app (Ter (Lam cs x t) e) u = eval (Pair e (x,u)) t
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

projVal :: String -> Val -> Val
projVal l (VRecord fs)    = case lookup l fs of
  Just x -> x
  Nothing -> error $ "projVal: could not find field " ++ show l
projVal l u | isNeutral u = VProj l u
            | otherwise   = error $ show u ++ " should be neutral"

convs :: Int -> [Val] -> [Val] -> Maybe D
convs k a b = mconcat $ zipWith (conv k) a b

equal :: (Pretty a, Eq a) => a -> a -> Maybe D
equal a b | a == b = Nothing
          | otherwise = different a b

different :: (Pretty a) => a -> a -> Maybe D
different a b = Just $ sep [pretty a,"/=",pretty b]

noSub :: (Pretty a) => a -> a -> Maybe D
noSub a b = Just $ sep [pretty a,"not a subtype of",pretty b]

-- | @conv k a b@ Checks that @a@ can be converted to @b@.
conv :: Int -> Val -> Val -> Maybe D
conv _ VU VU = Nothing
conv k (VLam f) (VLam g) = do
  let v = mkVar k
  conv (k+1) (f v) (g v)
conv k (VLam f) g = do
  let v = mkVar k
  conv (k+1) (f v) (app g v)
conv k f (VLam g) = do
  let v = mkVar k
  conv (k+1) (app f v) (g v)
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
  conv k u' u  <> conv (k+1) (app v w) (app v' w)
conv k (VRecordT fs) (VRecordT fs') = 
  convTele k fs fs'
conv k (VProj l u) (VProj l' u') = equal l l' <> conv k u u'
conv k (VCon c us) (VCon c' us') =
  (c `equal` c') <> mconcat (zipWith (conv k) us us')
conv k (VRecord fs) (VRecord fs') = convFields k fs fs'
conv k (VApp u v)   (VApp u' v')   = conv k u u' <> conv k v v'
conv k (VSplit u v) (VSplit u' v') = conv k u u' <> conv k v v'
conv _ (VVar x)     (VVar x')      = x `equal` x'
conv _ (VAbstract n) (VAbstract n') = n `equal` n'
conv _ (VPrim _ _) (VPrim _ _) = Nothing
conv _ x              x'           = different x x'

-- @sub _ a b@: check that a is a subtype of b.
sub :: Int -> Val -> Val -> Maybe D
sub _ VU VU = Nothing
sub k (VPi u v) (VPi u' v') = do
  let w = mkVar k
  conv k u' u  <> sub (k+1) (app v w) (app v' w)
sub k (VRecordT fs) (VRecordT fs') = subTele k fs fs'
sub k (VJoin a b) c = sub k a c <> sub k b c
sub k (VMeet a b) c = sub k a c `orElse` sub k b c
sub k c (VJoin a b) = sub k c a `orElse` sub k c b
sub k c (VMeet a b) = sub k c a <> sub k c b
sub k x x' = conv k x x'

orElse :: Maybe D -> Maybe D -> Maybe D
orElse Nothing _ = Nothing
orElse _ Nothing = Nothing
orElse (Just x) (Just y) = Just (x <> " and " <> y)

convEnv :: Int -> Env -> Env -> Maybe D
convEnv k e e' = mconcat $ zipWith (conv k) (valOfEnv e) (valOfEnv e')

convTele :: Int -> VTele -> VTele -> Maybe D
convTele _ VEmpty VEmpty = Nothing
convTele k (VBind l a t) (VBind l' a' t') = do
  let v = mkVar k
  equal l l' <> conv k a a' <> convTele (k+1) (t v) (t' v)
convTele _ x x' = different x x'

subTele :: Int -> VTele -> VTele -> Maybe D
subTele _ _ VEmpty = Nothing  -- all records are a subrecord of the empty record
subTele k (VBind l a t) (VBind l' a' t') = do
  let v = mkVar k
  if l == l'
    then sub k a a' <> subTele (k+1) (t v) (t' v)
    else subTele (k+1) (VBind l a t) (t' v)
subTele _ x x' = noSub x x'
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
  (VCon c us)  -> prn 4 (pretty c <+> showArgs us)
  (VPi a f)    -> pp 1 $ \p ->
    do s <- getSupply      -- "Pi" <+> svs [a,f]
       let b = app f (VVar s)
           depends = s `elem` unknowns b
       ((if depends
         then parens (pretty s <> ":" <> pretty a)
         else showVal 2 a)
         <+> "->") </> p b
  (VApp u v)   -> pp 4 (\p -> hang 2 (p u) (showVal 5 v))
  (VSplit u v) -> pretty u <+> showVal 5 v
  (VVar x)     -> pretty x
  (VRecordT tele) -> pretty tele
  (VRecord fs)   -> tupled [pretty l <+> "=" <+> pretty e | (l,e) <- fs]
  (VProj f u)     -> pp 5 (\p -> p u <> "." <> pretty f)
  (VLam f)  -> pp 1 $ \p -> do
    s <- getSupply
    hang 0 ("\\" <> pretty s <+> "->") (p (f $ VVar s))
  (VPrim _ nm) -> pretty nm
  (VAbstract nm) -> pretty ('#':nm)
 where pp :: Int -> ((Val -> D) -> D) -> D
       pp opPrec k = prn opPrec (k (showVal opPrec))
       prn opPrec = (if opPrec < ctx then parens else id)

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
prettyTele (VBind nm ty rest) = (pretty nm <+> ":" <+> pretty ty) : prettyTele (rest $ VVar nm)

instance Pretty VTele where
  pretty = encloseSep "[" "]" ";" . prettyTele

instance Pretty Env where
  pretty e = encloseSep "[" "]" ";" $ reverse (showEnv e)

showEnv :: Env -> [D]
showEnv e0 = case e0 of
    Empty            -> []
    (PDef _xas env)   -> showEnv env
    (Pair env ((x,_),u)) -> (pretty x <> "=" <> pretty u) : showEnv env

instance Pretty Ter where
  pretty = showTer 0 Empty

showTele :: Env -> Tele -> [D]
showTele ρ [] = mempty
showTele ρ (((x,_loc),t):tele) = (pretty x <> " : " <> showTer 0 ρ t) : showTele ρ tele

showTer :: Int -> Env -> Ter -> D
showTer ctx ρ t0 = case t0 of
   U             -> "U"
   (Meet e0 e1)  -> pp 2 $ \p -> p e0 <+> "/\\" <+> p e1
   (Join e0 e1)  -> pp 2 $ \p -> p e0 <+> "\\/" <+> p e1
   (App e0 e1)   -> pp 4 $ \p -> p e0 <+> showTer 5 ρ e1
   (Pi a (Lam ("_",_) t)) -> pp 1 $ \p -> (showTer 2 ρ a <+> "->") </> p t
   (Pi a (Lam x t)) -> pp 1 $ \p -> (parens (pretty x <> ":" <> showTer 0 ρ a) <+> "->") </> p t
   (Pi e0 e1)    -> "Pi" <+> showTersArgs ρ [e0,e1]
   (Lam (x,_) e) -> pp 2 (\p -> hang 0 ("\\" <> pretty x <+> "->") (p e))
   (Proj l e)    -> pp 5 (\p -> p e <> "." <> pretty l)
   (RecordT ts)  -> encloseSep "[" "]" ";" (showTele ρ ts)
   (Record fs)   -> encloseSep "(" ")" "," [pretty l <> " = " <> showTer 0 ρ e | (l,e) <- fs]
   (Where e d)   -> pp 0 (\p -> p e <+> "where" <+> showDecls ρ d)
   (Var x)       -> prettyLook x ρ
   (Con c es)    -> pretty c <+> showTersArgs ρ es
   (Split _l branches)   -> hang 2 "split"  $ showSplitBranches ρ branches
   (Sum (_name,_) branches) -> encloseSep "{" "}" "| " (map (showBranch ρ) branches)
   (Undef _)     -> "undefined (1)"
   (Real r)      -> showy r
   (Prim n)      -> showy n
 where pp :: Int -> ((Ter -> D) -> D) -> D
       pp opPrec k = prn opPrec (k (showTer opPrec ρ))
       prn opPrec = (if opPrec < ctx then parens else id)


showSplitBranches ρ branches = encloseSep "{" "}" ";"
  [hang 2 (pretty l <+> sep (map (pretty . fst) bnds) <+> "↦") (showTer 0 ρ t)  | (l,(bnds,t)) <- branches]
  
showBranch :: Env -> (Binder, Tele) -> D
showBranch env ((b,_),tele) = pretty b <+> sep (map parens (showTele env tele))
instance Pretty Loc where
  pretty (Loc x l) = pretty x <> "@" <> pretty l

showTersArgs :: Env -> [Ter] -> D
showTersArgs ρ = hcat . map (showTer 5 ρ)

showDecl :: forall a. Pretty a => Env -> (a, Ter, Ter) -> D
showDecl ρ (b,typ,ter) = vcat [pretty b <+> ":" <+> showTer 0 ρ typ,
                               pretty b <+> "=" <+> showTer 0 ρ ter]
showDecls :: Env -> Decls -> D
showDecls ρ defs = vcat (map (showDecl ρ) defs)

class Value v where
  unknowns :: v -> [String] -- aka "free variables"

instance Value Val where
  unknowns v0 = case v0 of
    VU -> []
    VPi x y -> unknowns x ++ unknowns y
    VRecordT x -> unknowns x
    VRecord x -> concatMap (unknowns . snd) x
    VCon _ x -> concatMap unknowns x
    VApp x y -> unknowns x ++ unknowns y
    VSplit x y -> unknowns x ++ unknowns y
    VProj _ x -> unknowns x
    VLam f -> unknowns (f (VVar "___UNK___"))
    VPrim{} -> []
    VAbstract{} -> []
    VMeet x y -> unknowns x ++ unknowns y
    VJoin x y -> unknowns x ++ unknowns y
    VVar x -> [x]
    Ter _ env -> unknowns env

instance Value Env where
  unknowns Empty = []
  unknowns (Pair env (_,u)) = unknowns env ++ unknowns u
  unknowns (PDef _ env) = unknowns env

instance Value VTele where
  unknowns VEmpty = []
  unknowns (VBind _ x y) = unknowns x ++ unknowns (y (VVar "___UNK___"))
  unknowns VBot = []

  
