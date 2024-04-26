module Optimize where

import Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4 )
import Subst (subst, shiftIndexes)
import Utils (semOp, usesLetInBody, treeChanged)
import Common ( Pos )

deadCodeElimination :: MonadFD4 m => TTerm -> m TTerm
deadCodeElimination (Let p v ty def (Sc1 t)) = hasEffects def >>= \e ->
  if usesLetInBody t || e 
  then do 
          def' <- deadCodeElimination def
          t' <- deadCodeElimination t
          return $ Let p v ty def' (Sc1 t')
  else deadCodeElimination (shiftIndexes t)
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

hasEffects :: MonadFD4 m => TTerm -> m Bool
hasEffects (V _ (Bound _)) = return False
hasEffects (V _ (Free _)) = return False
hasEffects (V _ (Global n)) = do 
                                lt <- lookupDecl n
                                case lt of
                                  Nothing -> failFD4 "Variable no declarada"
                                  Just t -> hasEffects t
hasEffects (Const _ _) = return False
hasEffects (Print _ str t) = return True
hasEffects (IfZ _ c t1 t2) = do
                                cb <- hasEffects c 
                                t1b <- hasEffects t1 
                                t2b <- hasEffects t2
                                return (cb || t1b || t2b)
hasEffects (Lam _ _ _ (Sc1 t)) = hasEffects t
hasEffects (App _ t u) = do
                          tb <- hasEffects t 
                          ub <- hasEffects u
                          return (tb || ub)
hasEffects (Fix _ _ _ _ _ (Sc2 t)) = return True
hasEffects (Let _ _ _ def (Sc1 t)) = do
                                        defb <- hasEffects def 
                                        tb <- hasEffects t
                                        return (defb || tb)
hasEffects (BinaryOp p op t1 t2) = do 
                                      t1b <- hasEffects t1 
                                      t2b <- hasEffects t2
                                      return (t1b || t2b)

optimizeDecl :: MonadFD4 m  => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p n ty t) = do
                                  t' <- optimizeTerm t 20
                                  return (Decl p n ty t')

optimizeTerm :: MonadFD4 m  => TTerm -> Int -> m (TTerm)
optimizeTerm t n = do 
                            t1 <- constantFolding t
                            t2 <- deadCodeElimination t1
                            if n > 1 && treeChanged t t2 
                              then optimizeTerm t2 (n-1)
                              else return t2