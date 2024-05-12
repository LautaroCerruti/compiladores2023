module Optimize where

import Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4 )
import Subst (subst, shiftIndexes, substWhileFixingIndexes)
import Utils (semOp, usesLetInBody, treeChanged, hasEffects, termSize)
import Common 
import Global
import Data.List

deadCodeElimination :: MonadFD4 m => TTerm -> m TTerm
deadCodeElimination (Let p v ty def (Sc1 t)) = do 
                                                  he <- hasEffects def
                                                  t' <- deadCodeElimination t
                                                  if usesLetInBody t' || he
                                                  then do
                                                        def' <- deadCodeElimination def
                                                        return $ Let p v ty def' (Sc1 t')
                                                  else return $ shiftIndexes t'
deadCodeElimination (Print p str t) = deadCodeElimination t >>= \t' -> return $ Print p str t'
deadCodeElimination (IfZ p c t1 t2) = do 
                                        c' <- deadCodeElimination c
                                        t1' <- deadCodeElimination t1
                                        t2' <- deadCodeElimination t2
                                        return $ IfZ p c' t1' t2'
deadCodeElimination (Lam p v ty (Sc1 t)) = deadCodeElimination t >>= \t' -> return $ Lam p v ty (Sc1 t')
deadCodeElimination (App p t u) = do 
                                    t' <- deadCodeElimination t
                                    u' <- deadCodeElimination u
                                    return $ App p t' u'
deadCodeElimination (Fix p f fty x xty (Sc2 t)) = deadCodeElimination t >>= \t' -> return $ Fix p f fty x xty (Sc2 t')
deadCodeElimination (BinaryOp p op tf ts) = do 
                                              tf' <- deadCodeElimination tf
                                              ts' <- deadCodeElimination ts
                                              return $ BinaryOp p op tf' ts'
deadCodeElimination t = return t

constantPropagation :: MonadFD4 m => TTerm -> Scope (Pos,Ty) Var -> m TTerm
constantPropagation u t = return $ subst u t

constantFolding :: MonadFD4 m => TTerm -> m TTerm
constantFolding t@(V _ (Bound _)) = return t
constantFolding t@(V _ (Free _)) = return t
constantFolding t@(V p (Global n)) = do 
                                      lt <- lookupDecl n
                                      case lt of
                                        Nothing -> failFD4 "Variable no declarada"
                                        Just (Const _ num@(CNat _)) -> return (Const p num)
                                        Just _ -> return t
constantFolding t@(Const _ (CNat _)) = return t
constantFolding (Print p str t) = do 
                                    t' <- constantFolding t
                                    return (Print p str t')
constantFolding (IfZ p c t1 t2) = do
                                    c'  <- constantFolding c
                                    case c' of
                                      Const _ (CNat 0) -> constantFolding t1
                                      Const _ (CNat _) -> constantFolding t2
                                      _                -> do 
                                                            t1' <- constantFolding t1
                                                            t2' <- constantFolding t2
                                                            return (IfZ p c' t1' t2')
constantFolding (Lam p v ty (Sc1 t)) = do
                                  t' <- constantFolding t
                                  return (Lam p v ty (Sc1 t'))
constantFolding (App p t u) = do
                                t' <- constantFolding t
                                u' <- constantFolding u
                                return (App p t' u')
constantFolding (Fix p f fty x xty (Sc2 t)) = do
                                          t' <- constantFolding t
                                          return (Fix p f fty x xty (Sc2 t'))
constantFolding (Let p v ty def (Sc1 t)) = do
                                      def' <- constantFolding def
                                      case def' of
                                        (Const _ _) -> do t' <- constantPropagation def' (Sc1 t)
                                                          t'' <- constantFolding t'
                                                          return (Let p v ty def' (Sc1 t''))
                                        _           -> do t' <- constantFolding t
                                                          return (Let p v ty def' (Sc1 t'))
constantFolding (BinaryOp p op tf ts) = do t1' <- constantFolding tf
                                           t2' <- constantFolding ts
                                           bopFold op t1' t2'
          where bopFold :: MonadFD4 m => BinaryOp -> TTerm -> TTerm -> m TTerm
                bopFold _ t (Const _ (CNat 0)) = return t
                bopFold Add (Const _ (CNat 0)) t = return t
                bopFold Sub c@(Const _ (CNat 0)) t = do
                                                        b <- hasEffects t
                                                        if b then return (BinaryOp p op c t) else return c
                bopFold _ (Const _ (CNat n1)) (Const _ (CNat n2)) = return $ Const p (CNat (semOp op n1 n2)) 
                bopFold Add (BinaryOp p1 Add t1 t2) t3 = do
                                                          t2b <- hasEffects t2
                                                          t3b <- hasEffects t3
                                                          if t2b || t3b 
                                                            then return (BinaryOp p Add (BinaryOp p1 Add t1 t2) t3)
                                                            else
                                                              do t4 <- constantFolding (BinaryOp p Add t2 t3)
                                                                 constantFolding (BinaryOp p Add t1 t4)
                bopFold Sub (BinaryOp p1 Sub t1 t2) t3 = do
                                                          t2b <- hasEffects t2
                                                          t3b <- hasEffects t3
                                                          if t2b || t3b 
                                                            then return (BinaryOp p Sub (BinaryOp p1 Sub t1 t2) t3)
                                                            else
                                                              do t4 <- constantFolding (BinaryOp p Add t2 t3)
                                                                 constantFolding (BinaryOp p Sub t1 t4)
                bopFold _ t1' t2'  = return (BinaryOp p op t1' t2')

isFix :: TTerm -> Bool
isFix (Fix _ _ _ _ _ _) = True
isFix _ = False

appsForFix :: TTerm -> Bool
appsForFix (App _ t _) = appsForFix t
appsForFix (Fix _ _ _ _ _ _) = True
appsForFix _ = False

isAppNBound :: Int -> TTerm -> Bool
isAppNBound n (App _ t _) = isAppNBound n t
isAppNBound n (V _ (Bound bid)) = n == bid 
isAppNBound _ _ = False

inlineExpansion :: MonadFD4 m => TTerm -> m TTerm
inlineExpansion (Let i n ty def sc@(Sc1 t)) = do 
                                                he <- hasEffects def
                                                defs <- termSize def
                                                if not he && defs < termSizeLimit
                                                then inlineExpansion $ substWhileFixingIndexes def sc
                                                else do 
                                                        def' <- inlineExpansion def
                                                        t' <- inlineExpansion t
                                                        return $ Let i n ty def' (Sc1 t')
inlineExpansion (App p l@(Lam i n ty sc@(Sc1 t)) u) = do 
                                                  he <- hasEffects u
                                                  us <- termSize u
                                                  if not he && us < termSizeLimit
                                                  then inlineExpansion $ substWhileFixingIndexes u sc
                                                  else do
                                                          t' <- inlineExpansion t
                                                          u' <- inlineExpansion u
                                                          return $ Let i n ty u' (Sc1 t')
inlineExpansion (App p g@(V _ (Global n)) u) = do 
                                                  lt <- lookupDecl n
                                                  case lt of
                                                    Nothing -> failFD4 "Variable no declarada"
                                                    Just t -> do 
                                                                ts <- termSize t
                                                                if ts < termSizeLimit
                                                                then inlineExpansion $ App p t u
                                                                else do u' <- inlineExpansion u
                                                                        return $ App p g u'
inlineExpansion app@(App p t u) = if appsForFix app 
                                  then inlineExpansionForFix app
                                  else do 
                                          t' <- inlineExpansion t
                                          u' <- inlineExpansion u
                                          return $ App p t' u'
inlineExpansion (Print p str t) = inlineExpansion t >>= \t' -> return $ Print p str t'
inlineExpansion (IfZ p c t1 t2) = do 
                                        c' <- inlineExpansion c
                                        t1' <- inlineExpansion t1
                                        t2' <- inlineExpansion t2
                                        return $ IfZ p c' t1' t2'
inlineExpansion (Lam p v ty (Sc1 t)) = inlineExpansion t >>= \t' -> return $ Lam p v ty (Sc1 t')
inlineExpansion (Fix p f fty x xty (Sc2 t)) = inlineExpansion t >>= \t' -> return $ Fix p f fty x xty (Sc2 t')
inlineExpansion (BinaryOp p op tf ts) = do 
                                              tf' <- inlineExpansion tf
                                              ts' <- inlineExpansion ts
                                              return $ BinaryOp p op tf' ts'
inlineExpansion g@(V i (Global n)) = do 
                                      lt <- lookupDecl n
                                      case lt of
                                        Nothing -> failFD4 "Variable no declarada"
                                        Just t -> do 
                                                    ts <- termSize t
                                                    if ts < termSizeLimit 
                                                    then inlineExpansion t
                                                    else return g
inlineExpansion t = return t

getFixAndParams :: TTerm -> (TTerm, [TTerm])
getFixAndParams term = (getFix term, reverse $ getParams term)
  where 
        getFix f@(Fix _ _ _ _ _ _) = f
        getFix (App _ t _) = getFix t
        getFix _ = error "No es un Fix"
        getParams (Fix _ _ _ _ _ _) = []
        getParams (App _ t u) = u : (getParams t)
        getParams _ = error "No es un Fix"

getArgsCount :: TTerm -> Int
getArgsCount (Fix _ _ _ _ _ (Sc2 t)) = 1 + getArgsCount t
getArgsCount (Lam _ _ _ (Sc1 t)) = 1 + getArgsCount t
getArgsCount _ = 0

getFixBody :: TTerm -> TTerm
getFixBody (Fix _ _ _ _ _ (Sc2 t)) = getFixBody t
getFixBody (Lam _ _ _ (Sc1 t)) = getFixBody t
getFixBody t = t

getChangingParamsInApp :: Int -> Int -> TTerm -> [Int]
getChangingParamsInApp d n (App _ f (V _ (Bound i))) = if (d+n) == i then getChangingParamsInApp d (n+1) f else n : (getChangingParamsInApp d (n+1) f)
getChangingParamsInApp d n (App _ f _) = n : (getChangingParamsInApp d (n+1) f)
getChangingParamsInApp _ _ _ = [] 

applyGetChangingParamsToApp :: Int -> Int -> TTerm -> [Int]
applyGetChangingParamsToApp argsCount depth (App _ t u) = union (getChangingParams argsCount depth u) (applyGetChangingParamsToApp argsCount depth t)
applyGetChangingParamsToApp _ _ _ = []

getChangingParams :: Int -> Int -> TTerm -> [Int]
getChangingParams _ _ (V _ _) = []
getChangingParams _ _ (Const _ _) = []
getChangingParams argsCount depth (Lam _ _ _ (Sc1 t)) = getChangingParams argsCount (depth+1) t
getChangingParams argsCount depth app@(App _ t u) = 
  if isAppNBound (argsCount+depth) app
  then union (getChangingParamsInApp depth 0 app) (applyGetChangingParamsToApp argsCount depth app)
  else union (getChangingParams argsCount depth t) (getChangingParams argsCount depth u)
getChangingParams argsCount depth (Print _ _ t) = getChangingParams argsCount depth t
getChangingParams argsCount depth (BinaryOp _ _ t u) = union (getChangingParams argsCount depth t) (getChangingParams argsCount depth u)
getChangingParams argsCount depth (Fix _ _ _ _ _ (Sc2 t)) = getChangingParams argsCount (depth+2) t
getChangingParams argsCount depth (IfZ _ c t u) = union (getChangingParams argsCount depth c) (union (getChangingParams argsCount depth t) (getChangingParams argsCount depth u))
getChangingParams argsCount depth (Let _ _ _ d (Sc1 t)) = union (getChangingParams argsCount depth d) (getChangingParams argsCount (depth+1) t)

getNoChangingParams :: Int -> TTerm -> [Int]
getNoChangingParams argsCount (body) = let paramsChanging = getChangingParams argsCount 0 body 
                                           paramIdexes = [0 .. argsCount-1]
                                       in paramIdexes \\ paramsChanging 

data BType = AB | FB
  deriving (Show, Eq)

getBoundsInfo :: Int -> TTerm -> ((Int, BType, Name, Ty), [(Int, BType, Name, Ty)])
getBoundsInfo argsC (Fix inf fn fty an aty (Sc2 t)) = ((argsC, FB, fn, fty), getArgs (argsC-1) t ++ [(argsC-1, AB, an, aty)])
  where 
        getArgs n (Lam _ an' aty' (Sc1 t')) = getArgs (n-1) t' ++ [((n-1), AB, an', aty')]
        getArgs _ _ = []
getBoundsInfo _ _ = error "No es un fix"

deleteParams :: Int -> Int -> [Int] -> [Int] -> Int -> TTerm -> TTerm
deleteParams d argsC boundD boundC i (App p t u) = if elem i boundD then deleteParams d argsC boundD boundC (i+1) t else App p (deleteParams d argsC boundD boundC (i+1) t) (rewriteFixBody d argsC boundD boundC u)
deleteParams d argsC boundD boundC i t = rewriteFixBody d argsC boundD boundC t

-- depth -> argsCount -> argsBorrado -> arrayNuevosIndices -> Termino viejo -> Termino nuevo
rewriteFixBody :: Int -> Int -> [Int] -> [Int] -> TTerm -> TTerm
rewriteFixBody d argsC boundD boundC b@(V p (Bound i)) = if (i >= d && (i-d) <= argsC) then V p (Bound ((boundC !! ((i-d)))+d)) else b
rewriteFixBody _ _ _ _ b@(V _ _) = b
rewriteFixBody _ _ _ _ b@(Const _ _) = b
rewriteFixBody d argsC boundD boundC (Lam p n ty (Sc1 t)) = Lam p n ty (Sc1 (rewriteFixBody (d+1) argsC boundD boundC t))
rewriteFixBody d argsC boundD boundC app@(App p t u) = 
  if isAppNBound (argsC+d) app
  then deleteParams d argsC boundD boundC 0 app 
  else App p (rewriteFixBody d argsC boundD boundC t) (rewriteFixBody d argsC boundD boundC u)
rewriteFixBody d argsC boundD boundC (Print p str t) = Print p str (rewriteFixBody d argsC boundD boundC t)
rewriteFixBody d argsC boundD boundC (BinaryOp p bop t u) = BinaryOp p bop (rewriteFixBody d argsC boundD boundC t) (rewriteFixBody d argsC boundD boundC u)
rewriteFixBody d argsC boundD boundC (Fix p fn fty n ty (Sc2 t)) = Fix p fn fty n ty (Sc2 (rewriteFixBody (d+2) argsC boundD boundC t))
rewriteFixBody d argsC boundD boundC (IfZ p c t u) = IfZ p (rewriteFixBody d argsC boundD boundC c) (rewriteFixBody d argsC boundD boundC t) (rewriteFixBody d argsC boundD boundC u)
rewriteFixBody d argsC boundD boundC (Let p n ty def (Sc1 t)) = Let p n ty (rewriteFixBody d argsC boundD boundC def) (Sc1 (rewriteFixBody (d+1) argsC boundD boundC t))

fixType :: Int -> Int -> [Int] -> Ty -> Ty
fixType argsC n pc ty@(FunTy t1 t2 name) = 
  if n==argsC 
  then ty
  else 
    if elem n pc 
    then fixType argsC (n+1) pc t2 
    else FunTy t1 (fixType argsC (n+1) pc t2) name
fixType _ _ _ ty = ty

-- ver si los (NoPos, NatTy) estan bien
rewriteFixAux :: Int -> [Int] -> [(Int, BType, Name, Ty)] -> [Int] -> TTerm -> TTerm
rewriteFixAux argsC pc ((_, AB, n, ty):funInfo) inds fixB = Lam (NoPos, NatTy Nothing) n ty (Sc1 (rewriteFixAux argsC pc funInfo inds fixB))
rewriteFixAux argsC pc ((_, FB, fn, fty):((_, AB, n, ty):funInfo)) inds fixB = Fix (NoPos, NatTy Nothing) fn (fixType argsC 0 pc fty) n ty (Sc2 (rewriteFixAux argsC pc funInfo inds fixB))
rewriteFixAux argsC pc [] inds fixB = rewriteFixBody 0 argsC pc inds fixB
rewriteFixAux _ _ _ _ _ = error "No deberia llegar a aca"

rewriteFix :: MonadFD4 m => Int -> [Int] -> TTerm -> m TTerm
rewriteFix argsC pc t = let (fixD, argsD) = getBoundsInfo argsC t
                            ls = reverse (map (\i -> (argsD !! i)) pc)
                            le = reverse (argsD \\ ls)
                            no = ls ++ [fixD] ++ le
                            indexesAux = map (\(i, _, _, _) -> i) (reverse no)
                            indexes = map (\i -> case elemIndex i indexesAux of 
                                                    Just e -> e
                                                    Nothing -> error "No deberia pasar") [0 .. argsC]
                        in do return $ rewriteFixAux argsC pc no indexes (getFixBody t)

buildApp :: [TTerm] -> TTerm -> TTerm
buildApp [] fix = fix
buildApp (x:xs) fix = App (NoPos, NatTy Nothing) (buildApp xs fix) x

countArgs :: TTerm -> Int
countArgs (App _ t _) = 1 + countArgs t
countArgs _ = 0

applyCheckPartial2App :: Int -> Int -> TTerm -> Bool
applyCheckPartial2App d argsC (App p t u) = (applyCheckPartial2App d argsC t) || checkPartialApps d argsC u
applyCheckPartial2App _ _ _ = False

checkPartialApps :: Int -> Int -> TTerm -> Bool
checkPartialApps d argsC app@(App p t u) = 
  if isAppNBound (d+argsC) app 
  then countArgs app /= argsC || (applyCheckPartial2App d argsC app)
  else (checkPartialApps d argsC t) || (checkPartialApps d argsC u)
checkPartialApps d argsC (Lam _ _ _ (Sc1 t)) = checkPartialApps (d+1) argsC t
checkPartialApps d argsC (Print _ _ t) = checkPartialApps d argsC t
checkPartialApps d argsC (BinaryOp _ _ t u) = (checkPartialApps d argsC t) || (checkPartialApps d argsC u)
checkPartialApps d argsC (Fix _ _ _ _ _ (Sc2 t)) = checkPartialApps (d+2) argsC t
checkPartialApps d argsC (IfZ _ c t u) = (checkPartialApps d argsC c) || (checkPartialApps d argsC t) || (checkPartialApps d argsC u)
checkPartialApps d argsC (Let _ _ _ def (Sc1 t)) = (checkPartialApps d argsC def) || (checkPartialApps (d+1) argsC t)
checkPartialApps d argsC (V _ (Bound i)) = (d+argsC) == i
checkPartialApps _ _ _ = False

inlineExpansionForFix :: MonadFD4 m => TTerm -> m TTerm
inlineExpansionForFix app@(App p t u) = 
  let (fix, params) = getFixAndParams app 
      argsC = getArgsCount fix
  in 
    do 
    -- fixOpt <- optimizeTermFull fix
    -- printFD4 ("AAAAAA " ++ (show (checkPartialApps 0 argsC (getFixBody fix))))
    -- printFD4 ("BBBBBB " ++ (show (getFixBody fix)))
    if (length params) /= argsC || checkPartialApps 0 argsC (getFixBody fix) 
    then do t' <- inlineExpansion t -- Caso fix sin aplicar completamente
            u' <- inlineExpansion u
            return $ App p t' u'
    else 
      let ncp = sort $ getNoChangingParams argsC (getFixBody fix) 
      in if length ncp == 0 ||  length ncp == argsC
         then do 
                t' <- inlineExpansion t
                u' <- inlineExpansion u
                return $ App p t' u'
         else do 
              fix' <- rewriteFix argsC ncp fix
              let rParams = reverse params
                  npInit = reverse (map (\i -> (rParams !! i)) ncp)
                  npTail = reverse [x | (x, i) <- zip rParams [0..], not (i `elem` ncp)]
                  app' = buildApp (reverse (npInit ++ npTail)) fix'
              return $ app'
inlineExpansionForFix _ = failFD4 "No se puede hacer inline Expansion Fix de algo que no es un fix"

optimizeDecl :: MonadFD4 m  => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p n ty t) = do
                                  t' <- optimizeTerm t 100
                                  return (Decl p n ty t')

optimizeTermFull :: MonadFD4 m  => TTerm -> m (TTerm)
optimizeTermFull t = do 
                    t1 <- inlineExpansion t
                    t2 <- constantFolding t1
                    t3 <- deadCodeElimination t2
                    if treeChanged t t3 
                      then optimizeTermFull t3
                      else return t3

optimizeTerm :: MonadFD4 m  => TTerm -> Int -> m (TTerm)
optimizeTerm t n = do 
                    t1 <- inlineExpansion t
                    t2 <- constantFolding t1
                    t3 <- deadCodeElimination t2
                    if n > 1 && treeChanged t t3 
                      then optimizeTerm t3 (n-1)
                      else return t3