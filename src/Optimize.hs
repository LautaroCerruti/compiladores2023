module Optimize where

import Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4 )
import Utils (semOp)

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
                                      t' <- constantFolding t
                                      return (Let p v ty def' (Sc1 t'))
constantFolding (BinaryOp p op t1 t2) = do t1' <- constantFolding t1
                                           t2' <- constantFolding t2
                                           bopFold op t1' t2'
          where bopFold :: MonadFD4 m => BinaryOp -> TTerm -> TTerm -> m TTerm
                bopFold _ t (Const _ (CNat 0)) = return t
                bopFold Add (Const _ (CNat 0)) t = return t
                bopFold Sub c@(Const _ (CNat 0)) t = return c
                bopFold _ (Const _ (CNat n1)) (Const _ (CNat n2)) = return $ Const p (CNat (semOp op n1 n2)) 
                bopFold _ t1' t2'  = return (BinaryOp p op t1' t2')

optimizeDecl :: MonadFD4 m  => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p n ty t) = do 
                                  t' <- constantFolding t
                                  return (Decl p n ty t')
