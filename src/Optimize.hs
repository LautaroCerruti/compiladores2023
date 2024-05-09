module Optimize where

import Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4 )
import Subst (subst, shiftIndexes, substWhileFixingIndexes)
import Utils (semOp, usesLetInBody, treeChanged, hasEffects, termSize)
import Common ( Pos )
import Global
import Data.List ( union )

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
                                                                if ts < termSizeLimit -- && not (isFix t)
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
getFixAndParams term = (getFix term, getParams term)
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

getChangingParamsInApp :: Int -> TTerm -> [Int]
getChangingParamsInApp n (App _ f (V _ (Bound i))) = if n == i then getChangingParamsInApp (n+1) f else n : (getChangingParamsInApp (n-1) f)
getChangingParamsInApp n (App _ f _) = n : (getChangingParamsInApp (n+1) f)
getChangingParamsInApp _ _ = [] 

applyGetChangingParamsToApp :: Int -> Int -> TTerm -> [Int]
applyGetChangingParamsToApp argsCount depth (App _ t u) = union (getChangingParams argsCount depth u) (applyGetChangingParamsToApp argsCount depth t)
applyGetChangingParamsToApp _ _ _ = []

getChangingParams :: Int -> Int -> TTerm -> [Int]
getChangingParams _ _ (V _ _) = []
getChangingParams _ _ (Const _ _) = []
getChangingParams argsCount depth (Lam _ _ _ (Sc1 t)) = getChangingParams argsCount (depth+1) t
getChangingParams argsCount depth app@(App _ t u) = 
  if isAppNBound (argsCount+depth) app
  then union (getChangingParamsInApp depth app) (applyGetChangingParamsToApp argsCount depth app)
  else union (getChangingParams argsCount depth t) (getChangingParams argsCount depth u)
getChangingParams argsCount depth (Print _ _ t) = getChangingParams argsCount depth t
getChangingParams argsCount depth (BinaryOp _ _ t u) = union (getChangingParams argsCount depth t) (getChangingParams argsCount depth u)
getChangingParams argsCount depth (Fix _ _ _ _ _ (Sc2 t)) = getChangingParams argsCount (depth+2) t
getChangingParams argsCount depth (IfZ _ c t u) = union (getChangingParams argsCount depth c) (union (getChangingParams argsCount depth t) (getChangingParams argsCount depth u))
getChangingParams argsCount depth (Let _ _ _ d (Sc1 t)) = union (getChangingParams argsCount depth d) (getChangingParams argsCount (depth+1) t)

-- argsCount es el indice de la funcion recursiva
getNoChangingParams :: MonadFD4 m => Int -> TTerm -> m [Int]
getNoChangingParams argsCount (body) = let paramsChanging = getChangingParams argsCount 0 body in
                                      do printFD4 (" cambian " ++ (show (paramsChanging)))
                                         return []

inlineExpansionForFix :: MonadFD4 m => TTerm -> m TTerm
inlineExpansionForFix app@(App p t u) = 
  let (fix, params) = getFixAndParams app 
      argsCount = getArgsCount fix
  in
    if (length params) /= argsCount 
    then do t' <- inlineExpansion t -- Caso fix sin aplicar completamente
            u' <- inlineExpansion u
            return $ App p t' u'
    else do getNoChangingParams argsCount (getFixBody fix)
            t' <- inlineExpansion t -- Cambiar esto
            u' <- inlineExpansion u
            return $ App p t' u'
inlineExpansionForFix _ = failFD4 "No se puede hacer inline Expansion Fix de algo que no es un fix"

optimizeDecl :: MonadFD4 m  => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p n ty t) = do
                                  t' <- optimizeTerm t 100
                                  return (Decl p n ty t')

optimizeTerm :: MonadFD4 m  => TTerm -> Int -> m (TTerm)
optimizeTerm t n = do 
                    t1 <- inlineExpansion t
                    t2 <- constantFolding t1
                    t3 <- deadCodeElimination t2
                    if n > 1 && treeChanged t t3 
                      then optimizeTerm t3 (n-1)
                      else return t3