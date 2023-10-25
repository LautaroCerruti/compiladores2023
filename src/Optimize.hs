module Optimize where

import Lang
import MonadFD4 ( MonadFD4, lookupDecl, failFD4 )
import Subst (subst)
import Utils (semOp)
import Common ( Pos )

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
-- constantFolding convencional dejaria el If como esta, nosotros decidimos realizar la mejora de
-- sparse conditional constant propagation. Si la condicion evalua a una constante, ya sabemos que 
-- rama del Ifz es la que se va a ejecutar
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
                                                          constantFolding t'
                                        _           -> do t' <- constantFolding t
                                                          return (Let p v ty def' (Sc1 t'))
-- falta x + 4 - 3 y x + 4 + 3
constantFolding (BinaryOp p op t1 t2) = do t1' <- constantFolding t1
                                           t2' <- constantFolding t2
                                           bopFold op t1' t2'
          where bopFold :: MonadFD4 m => BinaryOp -> TTerm -> TTerm -> m TTerm
                bopFold _ t (Const _ (CNat 0)) = return t
                bopFold Add (Const _ (CNat 0)) t = return t
                bopFold Sub c@(Const _ (CNat 0)) t = if hasEffects t then return (BinaryOp p op c t) else return c
                bopFold _ (Const _ (CNat n1)) (Const _ (CNat n2)) = return $ Const p (CNat (semOp op n1 n2)) 
                bopFold _ t1' t2'  = return (BinaryOp p op t1' t2')

-- Esto podria estar monadizado y hacer que Global busque en el entorno y se fije si esa delcaracion tiene efectos
hasEffects :: TTerm -> Bool
hasEffects (V _ (Bound _)) = False
hasEffects (V _ (Free _)) = False
hasEffects (V _ (Global _)) = True
hasEffects (Const _ _) = False
hasEffects (Print _ str t) = True
hasEffects (IfZ _ c t1 t2) = hasEffects c || hasEffects t1 || hasEffects t2
hasEffects (Lam _ _ _ (Sc1 t)) = hasEffects t
hasEffects (App _ t u) = hasEffects t || hasEffects u
hasEffects (Fix _ _ _ _ _ (Sc2 t)) = True
hasEffects (Let _ _ _ def (Sc1 t)) = hasEffects def || hasEffects t
hasEffects (BinaryOp p op t1 t2) = hasEffects t1 || hasEffects t2

optimizeDecl :: MonadFD4 m  => Decl TTerm -> m (Decl TTerm)
optimizeDecl (Decl p n ty t) = do 
                                  t' <- constantFolding t
                                  return (Decl p n ty t')
